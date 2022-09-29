#![allow(non_snake_case)]

#[macro_use]
extern crate criterion;
use criterion::Criterion;

extern crate bulletproofs;
extern crate curve25519_dalek;
extern crate merlin;
extern crate rand;

use bulletproofs::ZKInnerProductProof;
use bulletproofs::{BulletproofGens, PedersenGens};
use core::iter;
use curve25519_dalek::ristretto::RistrettoPoint;
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::VartimeMultiscalarMul;
use merlin::Transcript;
use sha3::Sha3_512;


/// Different zkIPP input vector lengths to try
static TEST_SIZES: [usize; 69] = [
    18, 34, 66, 132, 262, 522, 1044, 2086, 4170, 8340, 16678, 33354, 66708, 133414, 266826, 533652, 1067302, 2134602,
    68, 134, 266, 532, 1062, 2122, 4244, 8486, 16970, 33940, 67878, 135754, 271508, 543014, 1086026, 2172052,
    194, 258, 388, 648, 1166, 2202, 4276, 8424, 16718, 33306, 66484, 132840, 265550, 530970, 1061812, 2123496, 4246862, 8493594,
    260, 390, 650, 1172, 2214, 4298, 8468, 16806, 33482, 66836, 133542, 266954, 533780, 1067430, 2134730, 4269332, 8538534,
];

fn create_zk_ipp_helper(c: &mut Criterion) {
    c.bench_function_over_inputs(
        "create_zk_ipp: ZK inner product proof creation",
        move |bench, n| {
            let mut transcript = Transcript::new(b"IPPBenchmark");

            let even_n = if *n > 1 {*n + *n % 2} else {*n};
            let mut aux = even_n;
            let mut padding = 0;
            while aux != 1 {
                if aux % 2 == 1 {padding = padding + 1}
                aux = (aux + aux % 2) / 2;        
            }

            let pedersen_gens = PedersenGens::default();
            let Q = pedersen_gens.B_blinding;
            // R would be determined upstream in the protocol, so we pick an arbitrary one.
            let R = RistrettoPoint::hash_from_bytes::<Sha3_512>(b"some point");

            let mut rng = rand::thread_rng();

            let bp_gens = BulletproofGens::new(even_n+padding, 1);
            let G_vec: Vec<RistrettoPoint> = bp_gens.share(0).G(even_n+padding).cloned().collect();
            let H_vec: Vec<RistrettoPoint> = bp_gens.share(0).H(even_n+padding).cloned().collect();

            let mut a_vec: Vec<Scalar> = (0..*n).map(|_| Scalar::random(&mut rng)).collect();
            let mut b_vec: Vec<Scalar> = (0..*n).map(|_| Scalar::random(&mut rng)).collect();
            if a_vec.len() > 1 && a_vec.len() % 2 != 0 {
                a_vec.push(Scalar::zero());
                b_vec.push(Scalar::zero());
            }

            let G_factors: Vec<Scalar> = iter::repeat(Scalar::one()).take(*n).collect();
            // y_inv is (the inverse of) a random challenge
            let y_inv = Scalar::random(&mut rng);
            let H_factors: Vec<Scalar> = exp_iter(y_inv).take(*n).collect();

            // F is chosen randomly by the verifier.
            let F = RistrettoPoint::random(&mut rng);
            // blinding factor in the commitment, known to prover.
            let alpha = Scalar::random(&mut rng);
            
            bench.iter(|| {
                ZKInnerProductProof::create(
                    &mut transcript,
                    &Q,
                    &R,
                    alpha,
                    &F,
                    &G_factors[..],
                    &H_factors[..],
                    G_vec.clone(),
                    H_vec.clone(),
                    a_vec.clone(),
                    b_vec.clone(),
                );
            })
        },
        TEST_SIZES,
    );
}

/// Provides an iterator over the powers of a `Scalar`.
///
/// This struct is created by the `exp_iter` function.
pub struct ScalarExp {
    x: Scalar,
    next_exp_x: Scalar,
}

impl Iterator for ScalarExp {
    type Item = Scalar;

    fn next(&mut self) -> Option<Scalar> {
        let exp_x = self.next_exp_x;
        self.next_exp_x *= self.x;
        Some(exp_x)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (usize::max_value(), None)
    }
}

/// Return an iterator of the powers of `x`.
pub fn exp_iter(x: Scalar) -> ScalarExp {
    let next_exp_x = Scalar::one();
    ScalarExp { x, next_exp_x }
}

/// Computes an inner product of two vectors
/// \\[
///    {\langle {\mathbf{a}}, {\mathbf{b}} \rangle} = \sum\_{i=0}^{n-1} a\_i \cdot b\_i.
/// \\]
/// Panics if the lengths of \\(\mathbf{a}\\) and \\(\mathbf{b}\\) are not equal.
pub fn inner_product(a: &[Scalar], b: &[Scalar]) -> Scalar {
    let mut out = Scalar::zero();
    if a.len() != b.len() {
        panic!("inner_product(a,b): lengths of vectors do not match");
    }
    for i in 0..a.len() {
        out += a[i] * b[i];
    }
    out
}

criterion_group! {
    name = create_zk_ipp;
    config = Criterion::default().sample_size(10);
    targets = create_zk_ipp_helper,
}

fn verify_zk_ipp_helper(c: &mut Criterion) {
    c.bench_function_over_inputs(
        "verify_zk_ipp: ZK inner product proof verification",
        move |bench, n| {
            let mut transcript = Transcript::new(b"IPPBenchmark");

            let pedersen_gens = PedersenGens::default();
            let Q = pedersen_gens.B_blinding;
            // R would be determined upstream in the protocol, so we pick an arbitrary one.
            let R = RistrettoPoint::hash_from_bytes::<Sha3_512>(b"some point");

            let mut rng = rand::thread_rng();

            let even_n = if *n > 1 {*n + *n % 2} else {*n};
            let mut aux = even_n;
            let mut padding = 0;
            while aux != 1 {
                if aux % 2 == 1 {padding = padding + 1}
                aux = (aux + aux % 2) / 2;        
            }

            let bp_gens = BulletproofGens::new(even_n+padding, 1);
            let G: Vec<RistrettoPoint> = bp_gens.share(0).G(even_n+padding).cloned().collect();
            let H: Vec<RistrettoPoint> = bp_gens.share(0).H(even_n+padding).cloned().collect();

            let mut a: Vec<Scalar> = (0..*n).map(|_| Scalar::random(&mut rng)).collect();
            let mut b: Vec<Scalar> = (0..*n).map(|_| Scalar::random(&mut rng)).collect();
            if a.len() > 1 && a.len() % 2 != 0 {
                a.push(Scalar::zero());
                b.push(Scalar::zero());
            }
            let ip = inner_product(&a, &b);

            let G_factors: Vec<Scalar> = iter::repeat(Scalar::one()).take(even_n).collect();
            // y_inv is (the inverse of) a random challenge
            let y_inv = Scalar::random(&mut rng);
            let H_factors: Vec<Scalar> = exp_iter(y_inv).take(even_n).collect();
            // F is chosen randomly by the verifier.
            let F = RistrettoPoint::random(&mut rng);
            // blinding factor in the commitment, known to prover.
            let alpha = Scalar::random(&mut rng);

            let ipp = ZKInnerProductProof::create(
                &mut transcript,
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

            // P would be determined upstream, but we need a correct P to check the proof.
            //
            // To generate P = <a,G> + <b,H'> + <a,b> Q, compute
            //             P = <a,G> + <b',H> + <a,b> Q,
            // where b' = b \circ y^(-n)
            let b_prime = b.iter().zip(exp_iter(y_inv)).map(|(bi, yi)| bi * yi);
            // a.iter() has Item=&Scalar, need Item=Scalar to chain with b_prime
            let a_prime = a.iter().cloned();

            let P = RistrettoPoint::vartime_multiscalar_mul(
                a_prime.chain(b_prime).chain(iter::once(ip)).chain(iter::once(alpha)),
                G.iter().take(even_n).chain(H.iter().take(even_n)).chain(iter::once(&Q)).chain(iter::once(&R)));

            // Verify ipp
            bench.iter(|| {
                let mut verifier = Transcript::new(b"IPPBenchmark");
                ipp.verify(
                    even_n,
                    &mut verifier,
                    y_inv,
                    &P,
                    &Q,
                    &R,
                    &F,
                    &G,
                    &H,
                );
            })
        },
        TEST_SIZES,
    );
}

criterion_group! {
    name = verify_zk_ipp;
    config = Criterion::default().sample_size(10);
    targets = verify_zk_ipp_helper,
}

criterion_main!(create_zk_ipp, verify_zk_ipp);
