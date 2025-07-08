use ark_std::{test_rng, UniformRand};
use crate::ntt::*;
use crate::cq::*;
use ark_bls12_381::Fr;
mod cq;
mod ntt;

fn main() {
    let mut rng = test_rng();
    let n_total = 32;
    let n = 4;
    
    // Generate t
    let t: Vec<Fr> = (0..n_total).map(|_| Fr::rand(&mut rng)).collect();
    
    // f is a subset of t
    let mut f: Vec<Fr> = t[..n].to_vec();
    
    // iNTT on f
    let fx: Vec<Fr> = intt(&f, n, &None);
    
    // Generate SRS
    let srs = generate(n_total, &t);
    
    // Commitment to f
    let cm = mul_vec(&srs.srs1[..n], &fx, n);
    
    // Run protocol
    is_in_table(cm, &t, n_total, &srs, n, &f);
}