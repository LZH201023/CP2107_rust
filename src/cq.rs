use std::collections::HashMap;
use std::time::Instant;
use ark_bls12_381::{Bls12_381, Fr, G1Projective as G1, G2Projective as G2};
use ark_ec::Group;
use ark_ec::pairing::Pairing;
use ark_ff::{UniformRand, Field, Zero, One};
use rand::thread_rng;
use ark_std::{log2, ops::{Add, Mul, Sub}};
use crate::ntt::*;
pub struct SRS {
    n: usize,
    pub(crate) srs1: Vec<G1>,
    srs2: Vec<G2>,
    zx2: G2,
    tx2: G2,
    qxs1: Vec<G1>,
    lxs1: Vec<G1>,
    lps1: Vec<G1>,
}

pub fn generate(n: usize, t: &[Fr]) -> SRS {
    let start = Instant::now();
    let mut rng = thread_rng();
    let mut x: Fr = Fr::rand(&mut rng);
    while x == Fr::zero() || x == Fr::one() {
        x = Fr::rand(&mut rng);
    }
    let mut a: Fr= Fr::ONE;
    let mut srs1 = Vec::with_capacity(n);
    let mut srs2 = Vec::with_capacity(n + 1);

    let g = G1::generator();
    let h = G2::generator();

    for _ in 0..n {
        srs1.push(g * &a);
        srs2.push(h * &a);
        a = a.mul(&x);
    }
    srs2.push(h.mul(&a));
    
    let zx2 = srs2[n] - &h;

    let mut ge = Some(-Fr::ONE);
    for _ in 1..log2(n) {
        ge = ge.and_then(|x| x.sqrt());
    }

    let T = intt(t, n, &ge);
    let tx2 = h.mul(eval_poly(&T, n - 1, &x));
    let ge = ge.unwrap();
    let qxs1 = fast_kzg(&T, n, &ge, &srs1);

    let mut lxs1 = ntt(&srs1, n);

    let half_n = n / 2;
    let n_inv = Fr::from(n as u64).inverse().unwrap();

    let mut temp: G1;
    for i in 1..half_n {
        temp = lxs1[i] * &n_inv;
        lxs1[i] = lxs1[n - i] * &n_inv;
        lxs1[n - i] = temp;
    }
    lxs1[0] *= &n_inv;
    lxs1[half_n] *= &n_inv;

    let mut lps1: Vec<G1> = Vec::with_capacity(n);
    let mut gi = Fr::one();
    for i in 0..n {
        lps1.push(lxs1[i] * &gi - srs1[n - 1] * &n_inv);
        gi /= &ge;
    }

    println!("Setup time: {:.2?}", start.elapsed());

    SRS {
        n,
        srs1,
        srs2,
        zx2,
        tx2,
        qxs1,
        lxs1,
        lps1,
    }
}

pub fn is_in_table(cm: G1, t: &[Fr], n_total: usize, srs: &SRS, n: usize, f: &[Fr]) {
    let mut rng = thread_rng();
    let mut verifier_timer: Instant;
    let mut prover_timer: Instant;
    let mut prover_time = std::time::Duration::ZERO;
    let mut verifier_time = std::time::Duration::ZERO;

    let mut table: HashMap<Fr, usize> = HashMap::new();
    for (i, &ti) in t.iter().enumerate() {
        table.insert(ti.clone(), i);
    }

    prover_timer = Instant::now();
    let mut m_table: HashMap<usize, usize> = HashMap::new();
    for &fi in f.iter() {
        if let Some(&idx) = table.get(&fi) {
            *m_table.entry(idx).or_insert(0) += 1;
        }
    }

    let mut tool = Fr::ONE.mul(Fr::ONE);
    let mut m = G1::zero();
    let mut coefficient: Fr;
    for (&idx, &count) in &m_table {
        coefficient = Fr::from(count as u64);
        m += srs.lxs1[idx].mul(coefficient);
    }
    prover_time += prover_timer.elapsed();
    println!("Prover's commitment m: {:?}", m);

    verifier_timer = Instant::now();
    let beta: Fr = Fr::rand(&mut rng);
    verifier_time += verifier_timer.elapsed();
    println!("Verifier: beta = {:?}", &beta);

    prover_timer = Instant::now();
    let mut A: HashMap<usize, Fr> = HashMap::new();
    for (&idx, &count) in &m_table {
        coefficient = Fr::from(count as u64);
        A.insert(idx, coefficient / (t[idx].add(&beta)));
    }

    let mut a = G1::zero();
    for (&idx, val) in &A {
        a += srs.lxs1[idx].mul(val);
    }
    println!("Prover's commitment a: {:?}", a);

    let mut qa = G1::zero();
    for (&idx, val) in &A {
        qa += srs.qxs1[idx].mul(val);
    }
    println!("Prover's commitment qa: {:?}", qa);

    let mut B = Vec::with_capacity(n);
    for i in 0..n {
        B.push(f[i].add(&beta).inverse().unwrap());
    }
    let mut ge = Some(-Fr::ONE);
    let log_n = log2(n);
    for _ in 1..log_n {
        ge = ge.and_then(|x| x.sqrt());
    }
    let bx = intt(&B, n, &ge);
    let b0 = mul_vec(&(srs.srs1), &bx[1..], n - 1);
    println!("Prover's commitment b0: {:?}", b0);

    let mut fx = intt(f, n, &None);
    fx[0] += &beta;
    let pdt = poly_multi(&bx, n - 1, &fx, n - 1);
    fx[0] -= &beta;
    let mut q_b = vec![Fr::ZERO; n - 1];
    poly_div_z(&pdt, 2 * n - 2, n, q_b.as_mut_slice());
    let qb = mul_vec(&srs.srs1, &q_b, n - 1);
    println!("Prover's commitment qb: {:?}", qb);

    let p = mul_vec(&srs.srs1[n_total - n + 1..], &bx[1..], n - 1);
    prover_time += prover_timer.elapsed();
    println!("Prover's commitment p: {:?}", p);

    verifier_timer = Instant::now();
    let e1 = Bls12_381::pairing(&a, &(srs.tx2));
    let e2 = Bls12_381::pairing(&qa, &(srs.zx2));
    let e3 = Bls12_381::pairing(m.sub(a.mul(&beta)), &(srs.srs2[0]));
    let mut check = e1.eq(&e2.add(&e3));
    let e1 = Bls12_381::pairing(&b0, &srs.srs2[n_total - n + 1]);
    let e2 = Bls12_381::pairing(&p, &srs.srs2[0]);
    check = check && e1.eq(&e2);
    verifier_time += verifier_timer.elapsed();
    if !check {
        println!("Verifier rejects");
        println!("Prover time: {:.2?}", prover_time);
        println!("Verifier time: {:.2?}", verifier_time);
        return;
    }

    verifier_timer = Instant::now();
    let gamma = Fr::rand(&mut rng);
    verifier_time += verifier_timer.elapsed();
    println!("Verifier: gamma = {:?}", &gamma);

    prover_timer = Instant::now();
    let b0g = eval_poly(&bx[1..], n - 2, &gamma);
    let fg = eval_poly(&fx, n - 1, &gamma);
    let ni = Fr::from(n_total as u64).inverse().unwrap();
    let mut a_0 = Fr::zero();
    for (_, &v) in &A {
        a_0 += v .mul(&ni);
    }
    prover_time += prover_timer.elapsed();
    println!("Prover: B0(gamma) = {:?}\nf(gamma) = {:?}\nA(0) = {:?}", &b0g, &fg, &a_0);

    verifier_timer = Instant::now();
    let b_0 = Fr::from(n_total as u64) * &a_0 * (Fr::from(n as u64).inverse().unwrap());
    let coefficient = gamma.pow(&[n as u64]);
    let qbg = ((b0g * gamma + b_0) * (fg + &beta) - Fr::one()) / (coefficient - Fr::one());
    let eta = Fr::rand(&mut rng);
    let v_v = &b0g + &eta.mul(&fg) + eta.square() * qbg;
    verifier_time += verifier_timer.elapsed();
    println!("Verifier: eta = {:?}", &eta);

    prover_timer = Instant::now();
    let v_p = &b0g + &eta.mul(&fg) + eta.square() * qbg;
    let coefficient = eta.square();
    for i in 0..(n - 1) {
        fx[i] *= &eta;
        fx[i] += &bx[i + 1];
        fx[i] += coefficient.mul(&q_b[i]);
    }
    fx[n - 1] *= eta;
    fx[0] -= v_p;

    let mut rem = fx[n - 1].clone();
    for i in (0..n - 1).rev() {
        let temp = fx[i].clone();
        fx[i] = rem;
        rem = temp + rem.mul(&gamma);
    }

    let pi = mul_vec(&srs.srs1, &fx, n - 1);
    prover_time += prover_timer.elapsed();
    println!("Prover's commitment pi: {:?}", pi);

    verifier_timer = Instant::now();
    let c = b0 + cm * &eta + qb * &coefficient;
    let e1 = Bls12_381::pairing(c - srs.srs1[0] * v_v + pi * &gamma, srs.srs2[0]);
    let e2 = Bls12_381::pairing(pi, srs.srs2[1]);
    let check = e1 == e2;
    verifier_time += verifier_timer.elapsed();
    if !check {
        println!("Verifier rejects");
        println!("Prover time: {:.2?}", prover_time);
        println!("Verifier time: {:.2?}", verifier_time);
        return;
    }

    prover_timer = Instant::now();
    let mut a0 = G1::zero();
    for (&idx, &val) in &A {
        a0 += &srs.lps1[idx].mul(&val);
    }
    prover_time += prover_timer.elapsed();
    println!("Prover's commitment a0: {:?}", a0);

    verifier_timer = Instant::now();
    let e1 = Bls12_381::pairing(a - srs.srs1[0] * &a_0, srs.srs2[0]);
    let e2 = Bls12_381::pairing(a0, srs.srs2[1]);
    let check = e1 == e2;
    verifier_time += verifier_timer.elapsed();
    if !check {
        println!("Verifier rejects");
        println!("Prover time: {:.2?}", prover_time);
        println!("Verifier time: {:.2?}", verifier_time);
        return;
    }

    println!("Verifier accepts");
    println!("Prover time: {:.2?}", prover_time);
    println!("Verifier time: {:.2?}", verifier_time);
}
fn eval_poly(poly: &[Fr], df: usize, i: &Fr) -> Fr {
    let mut x = Fr::one();
    let mut sum = Fr::zero();

    for j in 0..=df {
        sum = sum.add(x.mul(&poly[j]));
        x *= i;
    }

    sum
}
fn fast_kzg(t: &[Fr], n: usize, ge: &Fr, srs: &[G1]) -> Vec<G1> {
    let m = 2 * n;
    let mut s = vec![G1::zero(); m];
    for i in 0..n {
        s[i] = srs[n - 1 - i].clone();
    }
    for i in n..m {
        s[i] = G1::zero();
    }
    let mut s = ntt(&s, m);
    let mut v = vec![Fr::zero(); m];
    for i in (n + 1)..m {
        v[i] = t[i - n].clone();
    }
    let v = ntt(&v, m);

    for i in 0..m {
        s[i] *= &v[i];
    }

    let gm = ge.sqrt();
    let h = intt(&s, m, &gm);
    let mut proofs = ntt(&h[..n], n);

    let mut x = Fr::one().mul(Fr::one());
    let ni = Fr::from(n as u64).inverse().unwrap();
    for i in 0..n {
        proofs[i] *= x.mul(&ni);
        x *= ge;
    }
    proofs
}

fn poly_div_z(f: &[Fr], df: usize, m: usize, q: &mut[Fr]) {
    let n = df + 1;
    let mut r: Vec<Fr> = Vec::with_capacity(n);
    for i in 0..=df {
        r.push(f[i].clone());
    }
    for i in (0..=(n - m - 1)).rev() {
        q[i] = r[i + m].clone();
        r[i] = r[i].add(&q[i]);
    }
}

pub fn mul_vec(g: &[G1], s: &[Fr], n: usize) -> G1 {
    let mut c = G1::zero();
    for i in 0..n {
        c += g[i].mul(&s[i]);
    }
    c
}