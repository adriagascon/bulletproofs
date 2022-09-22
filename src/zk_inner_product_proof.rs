#![allow(non_snake_case)]
#![cfg_attr(feature = "docs", doc(include = "../docs/inner-product-protocol.md"))]

extern crate alloc;

use alloc::borrow::Borrow;
use alloc::vec::Vec;

use std::cmp;
use core::iter;
use crate::util;
use curve25519_dalek::ristretto::{CompressedRistretto, RistrettoPoint};
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::VartimeMultiscalarMul;
use merlin::Transcript;

use crate::errors::ProofError;
use crate::transcript::TranscriptProtocol;

#[derive(Clone, Debug)]
pub struct ZKInnerProductProof {
    pub(crate) L_vec: Vec<CompressedRistretto>,
    pub(crate) R_vec: Vec<CompressedRistretto>,
    pub(crate) lx: Scalar, // masked a, i.e. a + ra
    pub(crate) rx: Scalar, // masked b, i.e. b + rb
    pub(crate) cx: Scalar, // masked alpha, i.e. alpha + ralpha
    pub(crate) mx: Scalar, // masked delta, i.e. delta + rdelta
    pub(crate) taux: Scalar, // bliding factor in commitment T1*x + T2*x*x 
    pub(crate) T1: RistrettoPoint,  // commitment to t1 (1st coefficient of polynomial)
    pub(crate) T2: RistrettoPoint,  // commitment to t2 (2nd coefficient of polynomial)
    pub(crate) S: RistrettoPoint, // commitment to blinding factors ra, rb, rdelta
}

impl ZKInnerProductProof {    
    /// Create an inner-product proof.
    ///
    /// The proof is created with respect to the bases \\(G\\), \\(H'\\),
    /// where \\(H'\_i = H\_i \cdot \texttt{Hprime\\_factors}\_i\\).
    ///
    /// The `verifier` is passed in as a parameter so that the
    /// challenges depend on the *entire* transcript (including parent
    /// protocols).
    ///
    /// The lengths of the vectors must all be the same, and an even length.
    /// The requirement for even length is easysatisfy in general, by padding as in test_helper_create.
    pub fn create(
        transcript: &mut Transcript,
        Q: &RistrettoPoint,
        R: &RistrettoPoint,
        alpha: Scalar,
        F: &RistrettoPoint,
        G_factors: &[Scalar],
        H_factors: &[Scalar],
        mut G_vec: Vec<RistrettoPoint>,
        mut H_vec: Vec<RistrettoPoint>,
        mut a_vec: Vec<Scalar>,
        mut b_vec: Vec<Scalar>,
    ) -> ZKInnerProductProof {
        let mut n = a_vec.len();
        assert!(n % 2 == 0 || n == 1);
        let mut aux = n;
        let mut depth = 0;
        // This is to avoid dealing with floats in rust
        while aux != 1 {
            aux = (aux + aux % 2) / 2;
            depth = depth + 1;
        }

        // Create slices G,  G_padding, H, H_padding, a, b backed by their respective
        // vectors.  This lets us reslice as we compress the lengths
        // of the vectors in the main loop below.
        // G_padding, H_padding are used to pad the commit to inputs of odd lengths found
        // while "folding" the input recursively.
        let (mut G, G_padding) = G_vec.split_at_mut(n);
        let (mut H, H_padding) = H_vec.split_at_mut(n);
        let mut a = &mut a_vec[..];
        let mut b = &mut b_vec[..];

        // All of the input vectors must have the same length.
        assert_eq!(G.len(), n);
        assert_eq!(H.len(), n);
        assert_eq!(a.len(), n);
        assert_eq!(b.len(), n);
        assert_eq!(G_factors.len(), n);
        assert_eq!(H_factors.len(), n);

        // All of the input vectors must have a length that is a power of two.
        //assert!(n.is_power_of_two());
        assert!(n % 2 == 0 || n == 1);

        transcript.innerproduct_domain_sep(n as u64);

        let mut L_vec = Vec::with_capacity(depth);
        let mut R_vec = Vec::with_capacity(depth);

        let mut delta = Scalar::zero();

        let mut rng = rand::thread_rng();

        // If it's the first iteration, unroll the Hprime = H*y_inv scalar mults
        // into multiscalar muls, for performance.
        if n != 1 {
            n = n / 2;
            let (a_L, a_R) = a.split_at_mut(n);
            let (b_L, b_R) = b.split_at_mut(n);
            let (G_L, G_R) = G.split_at_mut(n);
            let (H_L, H_R) = H.split_at_mut(n);

            
            let c_L = inner_product_with_padding(&a_L, &b_R);
            let c_R = inner_product_with_padding(&a_R, &b_L);

            let delta_L = Scalar::random(&mut rng);
            let delta_R = Scalar::random(&mut rng);

            let L = RistrettoPoint::vartime_multiscalar_mul(
                a_L.iter()
                    .zip(G_factors[n..2 * n].into_iter())
                    .map(|(a_L_i, g)| a_L_i * g)
                    .chain(
                        b_R.iter()
                            .zip(H_factors[0..n].into_iter())
                            .map(|(b_R_i, h)| b_R_i * h),
                    )
                    .chain(iter::once(c_L)).chain(iter::once(delta_L)),
                G_R.iter().chain(H_L.iter()).chain(iter::once(Q)).chain(iter::once(F)),
            )
            .compress();

            let R = RistrettoPoint::vartime_multiscalar_mul(
                a_R.iter()
                    .zip(G_factors[0..n].into_iter())
                    .map(|(a_R_i, g)| a_R_i * g)
                    .chain(
                        b_L.iter()
                            .zip(H_factors[n..2 * n].into_iter())
                            .map(|(b_L_i, h)| b_L_i * h),
                    )
                    .chain(iter::once(c_R)).chain(iter::once(delta_R)),
                G_L.iter().chain(H_R.iter()).chain(iter::once(Q)).chain(iter::once(F)),
            )
            .compress();

            L_vec.push(L);
            R_vec.push(R);

            transcript.append_point(b"L", &L);
            transcript.append_point(b"R", &R);

            let u = transcript.challenge_scalar(b"u");
            let u_inv = u.invert();

            for i in 0..n {
                a_L[i] = a_L[i] * u + u_inv * a_R[i];
                b_L[i] = b_L[i] * u_inv + u * b_R[i];
                G_L[i] = RistrettoPoint::vartime_multiscalar_mul(
                    &[u_inv * G_factors[i], u * G_factors[n + i]],
                    &[G_L[i], G_R[i]],
                );
                H_L[i] = RistrettoPoint::vartime_multiscalar_mul(
                    &[u * H_factors[i], u_inv * H_factors[n + i]],
                    &[H_L[i], H_R[i]],
                )
            }

            delta = delta + delta_L * u * u + delta_R * u_inv * u_inv;

            a = a_L;
            b = b_L;
            G = G_L;
            H = H_L;
        }

        // Whenever in the process of folding the input we find an odd length, we pad a,b with a 0,
        // using generators in G_padding and H_padding.
        let mut current_padding_index = 0;
        while n != 1 {
            let (a_L,  a_R) = a.split_at_mut(n / 2 + n % 2);
            let (b_L,  b_R) = b.split_at_mut(n / 2 + n % 2);
            let (G_L,  G_R) = G.split_at_mut(n / 2 + n % 2);
            let (H_L,  H_R) = H.split_at_mut(n / 2 + n % 2);
            
            let c_L = inner_product_with_padding(&a_L, &b_R);
            let c_R = inner_product_with_padding(&a_R, &b_L);

            let delta_L = Scalar::random(&mut rng);
            let delta_R = Scalar::random(&mut rng);

            let G_R_padding: Vec<RistrettoPoint>;
            let H_R_padding: Vec<RistrettoPoint>;

            if n % 2 != 0 {
                G_R_padding = vec![G_padding[current_padding_index]];
                H_R_padding = vec![H_padding[current_padding_index]];
            } else {
                G_R_padding = vec![];
                H_R_padding = vec![];
            }
            
            let L = RistrettoPoint::vartime_multiscalar_mul(
                a_L.iter().chain(b_R.iter()).chain(iter::once(&c_L)).chain(iter::once(&delta_L)),
                G_R.iter().chain(G_R_padding.iter()).chain(H_L.iter().take(b_R.len())).chain(iter::once(Q)).chain(iter::once(F)),
            )
            .compress();

            let R = RistrettoPoint::vartime_multiscalar_mul(
                a_R.iter().chain(b_L.iter()).chain(iter::once(&c_R)).chain(iter::once(&delta_R)),
                G_L.iter().take(a_R.len()).chain(H_R.iter()).chain(H_R_padding.iter()).chain(iter::once(Q)).chain(iter::once(F)),
            )
            .compress();

            L_vec.push(L);
            R_vec.push(R);

            transcript.append_point(b"L", &L);
            transcript.append_point(b"R", &R);

            let u = transcript.challenge_scalar(b"u");
            let u_inv = u.invert();
            
            for i in 0..n/2 {
                a_L[i] = a_L[i] * u + u_inv * a_R[i];
                b_L[i] = b_L[i] * u_inv + u * b_R[i];
                G_L[i] = RistrettoPoint::vartime_multiscalar_mul(&[u_inv, u], &[G_L[i], G_R[i]]);
                H_L[i] = RistrettoPoint::vartime_multiscalar_mul(&[u, u_inv], &[H_L[i], H_R[i]]);
            }

            if n % 2 == 1 {
                let i = n/2;
                a_L[i] = a_L[i] * u;
                b_L[i] = b_L[i] * u_inv;
                G_L[i] = RistrettoPoint::vartime_multiscalar_mul(&[u_inv, u], &[G_L[i], G_padding[current_padding_index]]);
                H_L[i] = RistrettoPoint::vartime_multiscalar_mul(&[u, u_inv], &[H_L[i], H_padding[current_padding_index]]);
                current_padding_index = current_padding_index + 1;
            }

            delta = delta + delta_L * u * u + delta_R * u_inv * u_inv;
            
            a = a_L;
            b = b_L;
            G = G_L;
            H = H_L;
            n = n/2 + n % 2;
        }
        // In the base case the prover shows that P is of the form
        // P = R*alpha + F*delta + Q * (a * b) + G * a + H * b.

        // Base case
        // Sample blinding factors for a, b, and delta
        let ra = Scalar::random(&mut rng);
        let rb = Scalar::random(&mut rng);
        let ralpha = Scalar::random(&mut rng);
        let rdelta = Scalar::random(&mut rng);
        // S : commitment to blinding factors ra, rb, rdelta
        let S = RistrettoPoint::vartime_multiscalar_mul(
            iter::once(rdelta)
                .chain(iter::once(ra))
                .chain(iter::once(rb))
                .chain(iter::once(ralpha)),
            iter::once(F)
                .chain(G.iter())
                .chain(H.iter())
                .chain(iter::once(R))
        );

        // "Send" commitment to verifier
        transcript.append_point(b"S", &S.compress());

        // Verifier sends a challege x
        let x = transcript.challenge_scalar(b"x");
        print!("x =  ");
            for i in 0..32 {
                print!("{} ", x.as_bytes()[i]);
            }
        print!("\n");
        
        // Define masked witness lx, rx, mx, for challenge x
        let lx = a[0] + ra * x;
        let rx = b[0] + rb * x;
        let cx = alpha + ralpha * x;
        let mx = delta + rdelta * x;
        // lx * rx = (a + ra * x) * (b + rb * x) = a * b + (a*rb + b*ra)*x + ra*rb*x*x = t0 + t1*x + t2*x*x
        // T1: commitment to t1 with randomness tau1
        let t1 = a[0] * rb + b[0] * ra;
        let tau1 = Scalar::zero();//Scalar::random(&mut rng);
        let T1 = RistrettoPoint::vartime_multiscalar_mul(
            iter::once(tau1)
                .chain(iter::once(t1)),
            iter::once(F)
                .chain(iter::once(Q))
        );
        // T2: commitment to t2 with randomness tau2
        let t2 = ra * rb;
        let tau2 = Scalar::random(&mut rng);
        let T2 = RistrettoPoint::vartime_multiscalar_mul(
            iter::once(tau2)
                .chain(iter::once(t2)),
            iter::once(F)
                .chain(iter::once(Q))
        );
        // taux: blinding factor in commitment T1*x + T2*x*x 
        let taux = tau1 * x + tau2 * x * x;
        print!("delta (assignment) =  ");
        for i in 0..32 {
            print!("{} ", delta.as_bytes()[i]);
        }
        print!("\n");
        ZKInnerProductProof {
            L_vec: L_vec,
            R_vec: R_vec,
            lx: lx,
            rx: rx,
            cx: cx,
            mx: mx,
            taux: taux,
            T1: T1,
            T2: T2,
            S: S
        }
    }

    /// Computes three vectors of verification scalars \\([u\_{i}^{2}]\\), \\([u\_{i}^{-2}]\\) and \\([s\_{i}]\\) for combined multiscalar multiplication
    /// in a parent protocol. See [inner product protocol notes](index.html#verification-equation) for details.
    /// The verifier must provide the input length \\(n\\) explicitly to avoid unbounded allocation within the inner product proof.
    pub(crate) fn verification_scalars(
        &self,
        n: usize,
        transcript: &mut Transcript,
    ) -> Result<(Vec<Scalar>, Vec<Scalar>, Vec<Scalar>), ProofError> {
        let d = self.L_vec.len();
        if d >= 32 {
            // 4 billion multiplications should be enough for anyone
            // and this check prevents overflow in 1<<d below.
            return Err(ProofError::VerificationError);
        }
        
        if n.is_power_of_two() && (n != (1 << d)) {
            return Err(ProofError::VerificationError);
        }
        if n > (1 << d) {
            return Err(ProofError::VerificationError);
        }

        transcript.innerproduct_domain_sep(n as u64);
        if n == 1 {
            return  Ok((vec![], vec![], vec![]));
        }
        
        // 1. Recompute x_k,...,x_1 based on the proof transcript

        let mut challenges = Vec::with_capacity(d);
        for (L, R) in self.L_vec.iter().zip(self.R_vec.iter()) {
            transcript.validate_and_append_point(b"L", L)?;
            transcript.validate_and_append_point(b"R", R)?;
            let u = transcript.challenge_scalar(b"u");
            print!("\n");
            println!("challenge (prover) u = ");
            for i in 0..32 {
                print!("{} ", u.as_bytes()[i]);
            }
            print!("\n");

            challenges.push(u);
        }

        // 2. Compute 1/(u_k...u_1) and 1/u_k, ..., 1/u_1

        let mut challenges_inv = challenges.clone();
        Scalar::batch_invert(&mut challenges_inv);

        // 3. Compute u_i^2 and (1/u_i)^2
        let mut challenges_sq = challenges.clone();
        let mut challenges_inv_sq = challenges_inv.clone();
        for i in 0..d {
            // XXX missing square fn upstream
            challenges_sq[i] = challenges[i] * challenges[i];
            challenges_inv_sq[i] = challenges_inv[i] * challenges_inv[i];
        }

        // 4. Compute s values inductively.
        // M[i][1] tells us that the product of all challenges to which generator i is exponentiated.
        // Note that we have up to n + <log_n generators, because of the up to log_n additional ones used for padding.
        // For 1 <= i <= n, we have
        //     M[i][1] = challenges_inv[1]*M[i][2] if i <= n/2
        //     M[i][1] = challenges[1]*M[i-n/2][2] if i > n/2
        //
        // For n < i <= n+logn, we have
        //     M[i][1] = M[k][j] where level j>1 and position k is where generator i is used first for padding.
        //
        // For j > 1 and 1 <= i <= Lj, where Lj is the length of the vector at the jth level of the recursion
        //     M[i][j] = challenges_inv[j]*M[i][j+1] if i <= Lj/2
        //     M[i][j] = challenges[j]*M[i-Lj/2][j+1] if i <= Lj/2
        //
        // Base case:
        //     M[1][lg_n] = challenges_inv[log_n]
        //     M[2][lg_n] = challenges[log_n]

      
        let mut Ls: Vec<usize> = iter::repeat(0).take(d).collect();
        let mut aux = n;
        let mut depth = 0;
        let mut padded_levels = Vec::<usize>::with_capacity(d);
        while aux != 1 {
            if aux % 2 == 1 {padded_levels.push(depth)}
            Ls[depth] = aux + aux % 2;
            aux = (aux + aux % 2) / 2;
            depth = depth + 1;
        }
        assert!(depth == d);

        let mut s = Vec::<Scalar>::with_capacity(n+padded_levels.len());
        let mut M: Vec::<Vec<Scalar>>;

        // Initialize matrix to 0
        M = Vec::with_capacity(depth);
        for l in 0..depth {
            M.push(iter::repeat(Scalar::one()).take(Ls[l]).collect());
            assert!(Ls[l] % 2 == 0);
        }

        // Fill in matrix following the recursion "bottom-up"
        // base case
        M[depth - 1][0] = challenges_inv[depth - 1];
        M[depth - 1][1] = challenges[depth - 1];
        // recursive case
        for i in (0..depth-1).rev() {
            for j in 0..Ls[i] {
                if j < Ls[i] / 2 {
                    M[i][j] = challenges_inv[i] * M[i+1][j];
                } else {
                    M[i][j] = challenges[i] * M[i+1][j-Ls[i]/2];
                }
            }
        }
        
        for j in 0..n {
            s.push(M[0][j]);
        }
        
        for j in 0..padded_levels.len() {
            s.push(M[padded_levels[j]][Ls[padded_levels[j]]-1]);
        }

        Ok((challenges_sq, challenges_inv_sq, s))
    }

    #[allow(dead_code)]
    pub fn verify(
        &self,
        n: usize,
        transcript: &mut Transcript,
        y_inv: Scalar,
        P: &RistrettoPoint,
        Q: &RistrettoPoint,
        R: &RistrettoPoint,
        F: &RistrettoPoint,
        G: &[RistrettoPoint],
        H: &[RistrettoPoint],
    ) -> Result<(), ProofError>
    {
        let (u_sq, u_inv_sq, s) = self.verification_scalars(n, transcript)?;
        assert!(n == 1 || s.len() == G.len());
        let G_factors_padded: Vec<Scalar> = iter::repeat(Scalar::one()).take(G.len()).collect();
        let mut inv_s = s.clone();
        Scalar::batch_invert(&mut inv_s);
        let H_factors_padded: Vec<Scalar> = util::exp_iter(y_inv).take(n).chain(iter::repeat(Scalar::one()).take(G.len()-n)).collect();

        let Ls = self
            .L_vec
            .iter()
            .map(|p| p.decompress().ok_or(ProofError::VerificationError))
            .collect::<Result<Vec<_>, _>>()?;
        
        let Rs = self
            .R_vec
            .iter()
            .map(|p| p.decompress().ok_or(ProofError::VerificationError))
            .collect::<Result<Vec<_>, _>>()?;

        transcript.validate_and_append_point(b"S", &self.S.compress())?;
        let x = transcript.challenge_scalar(b"x");
        
        let P_basecase = if n == 1 {*P} else{
            RistrettoPoint::vartime_multiscalar_mul(
                iter::once(Scalar::one())
                    .chain(u_sq)
                    .chain(u_inv_sq),
                iter::once(P)
                    .chain(Ls.iter())
                    .chain(Rs.iter())
            )};

        let g_times_s = G_factors_padded
            .into_iter()
            .zip(s.iter())
            .map(|(g_i, s_i)| s_i * g_i.borrow());
        
        let h_times_s_inv = H_factors_padded
            .into_iter()
            .zip(inv_s)
            .map(|(h_i, s_i_inv)| s_i_inv * h_i.borrow());

        
        let G_basecase = if n == 1 {G[0]} else {
            RistrettoPoint::vartime_multiscalar_mul(
                g_times_s,
                G.iter()
            )};
        
        
        let H_basecase = if n == 1 {H[0]} else {
            RistrettoPoint::vartime_multiscalar_mul(
                    h_times_s_inv,
                H.iter()
            )};

        let expect_LHS = RistrettoPoint::vartime_multiscalar_mul(
            iter::once(Scalar::one())
                .chain(iter::once(x))
                .chain(iter::once(x*x))
                .chain(iter::once(x)),
            iter::once(P_basecase)
                .chain(iter::once(self.T1))
                .chain(iter::once(self.T2))
                .chain(iter::once(self.S))
            );
        let expect_RHS = RistrettoPoint::vartime_multiscalar_mul(
            iter::once(self.lx * self.rx)
                    .chain(iter::once(self.taux + self.mx))
                .chain(iter::once(self.lx))
                .chain(iter::once(self.rx))             
                .chain(iter::once(self.cx)),
            iter::once(Q)
                .chain(iter::once(F))
                .chain(iter::once(&G_basecase))
                .chain(iter::once(&H_basecase))
                .chain(iter::once(R))
        );
        // TODO: Merge the above multi-exponentiations into a single one for efficiency
        
        if expect_LHS == expect_RHS {
            Ok(())
        } else {
            Err(ProofError::VerificationError)
        }           
    }
}

/// Computes an inner product of two vectors
/// \\[
///    {\langle {\mathbf{a}}, {\mathbf{b}} \rangle} = \sum\_{i=0}^{n-1} a\_i \cdot b\_i.
/// \\]
/// if the lengths of \\(\mathbf{a}\\) and \\(\mathbf{b}\\) are off by one it pads with a zero, otherwise it panics.
pub fn inner_product_with_padding(a: &[Scalar], b: &[Scalar]) -> Scalar {
    let mut out = Scalar::zero();
    if cmp::max(a.len(), b.len()) - cmp::min(a.len(), b.len()) > 1 {
        panic!("inner_product(a,b): lengths of vectors are off by more than one");
    }
    for i in 0..cmp::min(a.len(), b.len()) {
        out += a[i] * b[i];
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::util;
    use sha3::Sha3_512;

    fn test_helper_create(n: usize) {
        let mut rng = rand::thread_rng();
        let even_n = if n > 1 {n + n%2} else {n};
        use crate::generators::BulletproofGens;
        let mut aux = even_n;
        let mut padding = 0;
        while aux != 1 {
            if aux % 2 == 1 {padding = padding + 1}
            aux = (aux + aux % 2) / 2;        
        }
        // We add one additional generator for each level of the recursion that will
        // be padded from odd to even length. These generators do not affect the commitment,
        // as it corresponds to padding a and b with a 0 if n is odd.
        let bp_gens = BulletproofGens::new(even_n+padding, 1);
        let G: Vec<RistrettoPoint> = bp_gens.share(0).G(even_n+padding).cloned().collect();
        let H: Vec<RistrettoPoint> = bp_gens.share(0).H(even_n+padding).cloned().collect();

        
        // Q would be determined upstream in the protocol, so we pick a random one.
        let Q = RistrettoPoint::hash_from_bytes::<Sha3_512>(b"test point");
        // R would be determined upstream in the protocol, so we pick a random one.
        let R = RistrettoPoint::hash_from_bytes::<Sha3_512>(b"another test point");

        // a and b are the vectors for which we want to prove c = <a,b>
        // If their length is odd we pad them with a zero.
        let mut a: Vec<_> = (0..n).map(|_| Scalar::random(&mut rng)).collect();
        let mut b: Vec<_> = (0..n).map(|_| Scalar::random(&mut rng)).collect();
        if a.len() > 1 && a.len() % 2 != 0 {
            a.push(Scalar::zero());
            b.push(Scalar::zero());
        }
        let c = inner_product_with_padding(&a, &b);

        let G_factors: Vec<Scalar> = iter::repeat(Scalar::one()).take(even_n).collect();

        // y_inv is (the inverse of) a random challenge
        // Adria: why is this y_inv needed?
        let y_inv = Scalar::random(&mut rng);
        let H_factors: Vec<Scalar> = util::exp_iter(y_inv).take(even_n).collect();

        // P would be determined upstream, but we need a correct P to check the proof.
        //
        // To generate P = <a,G> + <b,H'> + <a,b> Q, compute
        //             P = <a,G> + <b',H> + <a,b> Q,
        // where b' = b \circ y^(-n)
        let b_prime = b.iter().zip(util::exp_iter(y_inv)).map(|(bi, yi)| bi * yi);
        // a.iter() has Item=&Scalar, need Item=Scalar to chain with b_prime
        let a_prime = a.iter().cloned();

        let alpha = Scalar::random(&mut rng); // blinding factor in the commitment, known to prover.
        let P = RistrettoPoint::vartime_multiscalar_mul(
            a_prime.chain(b_prime).chain(iter::once(c)).chain(iter::once(alpha)),
            G.iter().take(even_n).chain(H.iter().take(even_n)).chain(iter::once(&Q)).chain(iter::once(&R)));
        
        // F is chosen randomly by the verifier. The prover will have to show that it knows delta so that
        // P + F*delta has the right form. This allows for the view of the verifier to be masked with itermediate
        // terms of the form F * delta', for random delta' known to prover only.
        let F = RistrettoPoint::random(&mut rng);

        let mut verifier = Transcript::new(b"innerproducttest");
        let proof = ZKInnerProductProof::create(
            &mut verifier,
            &Q,
            &R,
            alpha,
            &F,
            &G_factors,
            &H_factors,
            G.clone(),
            H.clone(),
            a.clone(),
            b.clone(),
        );

        let mut verifier = Transcript::new(b"innerproducttest");
        assert!(proof
                .verify(
                    even_n,
                    &mut verifier,
                    y_inv,
                    &P,
                    &Q,
                    &R,
                    &F,
                    &G,
                    &H
                )
                .is_ok());
    }



   
    #[test]
    fn make_ipp_1() {
        test_helper_create(1);
    }


    #[test]
    fn make_ipp_2() {
        test_helper_create(2);
    }

    #[test]
    fn make_ipp_4() {
        test_helper_create(4);
    }

    #[test]
    fn make_ipp_5() {
        test_helper_create(5);
    }

    #[test]
    fn make_ipp_23() {
        test_helper_create(23);
    }


    #[test]
    fn make_ipp_32() {
        test_helper_create(32);
    }

    
    #[test]
    fn make_ipp_42() {
        test_helper_create(42);
    }


    #[test]
    fn make_ipp_64() {
        test_helper_create(64);
    }

    #[test]
    fn test_inner_product() {
        let a = vec![
            Scalar::from(1u64),
            Scalar::from(2u64),
            Scalar::from(3u64),
            Scalar::from(4u64),
        ];
        let b = vec![
            Scalar::from(2u64),
            Scalar::from(3u64),
            Scalar::from(4u64),
            Scalar::from(5u64),
        ];
        assert_eq!(Scalar::from(40u64), inner_product_with_padding(&a, &b));
    }
}
