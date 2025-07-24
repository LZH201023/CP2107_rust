use std::collections::HashMap;
use std::ops::Div;
use std::time::Instant;
use ark_bls12_381::{Bls12_381, Fr, G1Projective as G1, G2Projective as G2};
use ark_ec::Group;
use ark_ec::pairing::Pairing;
use ark_ff::{UniformRand, Field, Zero, One};
use rand::thread_rng;
use ark_std::{log2, ops::{Add, Mul, Sub}};
use log::log;
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

    let ni = Fr::from(n_total as u64).inverse().unwrap();
    let mut a_0 = Fr::zero();
    for (_, &v) in &A {
        a_0 += v.mul(&ni);
    }
    let sum = a_0.mul(Fr::from(n_total as u64));
    println!("Prover: S = {:?}", &sum);

    let mut a0 = G1::zero();
    for (&idx, &val) in &A {
        a0 += &srs.lps1[idx].mul(&val);
    }
    prover_time += prover_timer.elapsed();
    println!("Prover's commitment a0: {:?}", a0);

    verifier_timer = Instant::now();
    let mut check = true;
    a_0 = sum.div(Fr::from(n_total as u64));
    let mut e1 = Bls12_381::pairing(a, srs.tx2);
    let mut e2 = Bls12_381::pairing(qa, srs.zx2);
    let mut e3 = Bls12_381::pairing(m.sub(a.mul(&beta)), srs.srs2[0]);
    check = check &&  (e1 == e2.add(&e3));
    e1 = Bls12_381::pairing(a.sub(srs.srs1[0].mul(&a_0)), srs.srs2[0]);
    e2 = Bls12_381::pairing(a0, srs.srs2[1]);
    check = check && (e1 == e2);
    verifier_time += verifier_timer.elapsed();
    if !check {
        println!("Verifier rejects");
        println!("Prover time: {:.2?}", prover_time);
        println!("Verifier time: {:.2?}", verifier_time);
        return;
    }

    prover_timer = Instant::now();
    let mut g: Vec<Fr> = Vec::with_capacity(n);
    for i in 0..n {
        g.push(f[i].add(&beta).inverse().unwrap());
    }
    let cm_g = commit(&g, n);

    let mut helper: Vec<Fr> = Vec::with_capacity(n);
    for i in 0..n {
        helper.push(g[i].clone());
    }
    prover_time += prover_timer.elapsed();

    //Sum-check on g
    println!("\nSumCheck1 starts");
    let log_n: usize = log2(n) as usize;
    let mut len = n;
    let mut current_sum: Fr = sum;
    let mut challenges: Vec<Fr> = Vec::with_capacity(log_n);
    for i in 0..log_n {
        prover_timer = Instant::now();
        let val0: Fr = helper[0..len / 2].iter().sum();
        let val1: Fr = helper[len / 2..len].iter().sum();
        len /= 2;
        println!("Iteration {}\nProver: {:?}\n{:?}", i, &val0, &val1);
        prover_time += prover_timer.elapsed();

        verifier_timer = Instant::now();
        check = check && (val0.add(&val1) == current_sum);
        if !check {
            verifier_time += verifier_timer.elapsed();
            println!("Verifier rejects");
            println!("Prover time: {:.2?}", prover_time);
            println!("Verifier time: {:.2?}", verifier_time);
            return;
        }
        let challenge: Fr = Fr::rand(&mut rng);
        println!("Verifier's challenge: {:?}", &challenge);
        challenges.push(challenge);
        current_sum = challenge.mul(&val1).add(val0.mul(Fr::ONE.sub(&challenge)));
        verifier_time += verifier_timer.elapsed();

        prover_timer = Instant::now();
        let mc = Fr::ONE.sub(&challenge);
        for i in 0..len {
            helper[i] = mc.mul(&helper[i]).add(challenge.mul(&helper[i + len]));
        }
        prover_time += prover_timer.elapsed();
    }

    //evaluate h at the random point (should be equal to current_sum)
    prover_timer = Instant::now();
    let witness = create_witness(&g, n, &challenges);
    println!("Evaluation: {:?}\nWitness: {:?}", &helper[0], &witness);
    prover_time += prover_timer.elapsed();

    verifier_timer = Instant::now();
    check = check && verify_evaluation(&g, n, &challenges, &helper[0]) && (helper[0] == current_sum);
    verifier_time += verifier_timer.elapsed();
    if !check {
        println!("Verifier rejects");
        println!("Prover time: {:.2?}", prover_time);
        println!("Verifier time: {:.2?}", verifier_time);
        return;
    }


    verifier_timer = Instant::now();
    let mut rr: Vec<Fr> = Vec::with_capacity(log_n);
    let mut r: Fr;
    println!("\nVerifier randomness :");
    for _ in 0..log_n {
        r = Fr::rand(&mut rng);
        println!("{:?}", &r);
        rr.push(r);
    }
    verifier_time = verifier_timer.elapsed();

    prover_timer = Instant::now();
    let mut h: Vec<Fr> = vec![Fr::ZERO; n];
    h[0] = Fr::ONE.sub(&rr[0]);
    h[1] = rr[0].clone();
    let mut step = 2;
    for i in 1..log_n {
        for j in (0..step).rev() {
            h[2 * j + 1] = h[j].mul(&rr[i]);
            h[2 * j] = h[j].mul(Fr::ONE.sub(&rr[i]));
        }
        step *= 2;
    }

    let mut helper1: Vec<Fr> = Vec::with_capacity(n);
    let mut helper2: Vec<Fr> = Vec::with_capacity(n);
    let mut helper3: Vec<Fr> = Vec::with_capacity(n);
    for i in 0..n {
        helper1.push(h[i].clone());
        helper2.push(g[i].clone());
        helper3.push(f[i].clone());
    }
    prover_time += prover_timer.elapsed();

    //final sum-check
    println!("\nSumCheck2 starts");
    len = n;
    let mut challenges: Vec<Fr> = Vec::with_capacity(log_n);
    current_sum = Fr::ONE;
    for j in 0..log_n {
        prover_timer = Instant::now();
        len /= 2;
        let mut val0: Fr = Fr::ZERO;
        let mut val1: Fr = Fr::ZERO;
        let mut val2: Fr = Fr::ZERO;
        let mut valm1: Fr = Fr::ZERO;
        for i in 0..len {
            val0 += helper1[i].mul(&helper2[i]).mul(beta.add(&helper3[i]));
            val1 += helper1[i + len].mul(&helper2[i + len]).mul(beta.add(&helper3[i + len]));
            val2 += Fr::from(2u64).mul(&helper1[i + len]).sub(&helper1[i])
                .mul(&Fr::from(2u64).mul(&helper2[i + len]).sub(&helper2[i]))
                .mul(&Fr::from(2u64).mul(&helper3[i + len]).sub(&helper3[i]).add(&beta));
            valm1 += Fr::from(2u64).mul(&helper1[i]).sub(&helper1[i + len])
                .mul(&Fr::from(2u64).mul(&helper2[i]).sub(&helper2[i + len]))
                .mul(&Fr::from(2u64).mul(&helper3[i]).sub(&helper3[i + len]).add(&beta));
        }
        println!("Iteration {}\nProver: {:?}\n{:?}\n{:?}\n{:?}", j, &val0, &val1, &val2, &valm1);
        prover_time += prover_timer.elapsed();

        verifier_timer = Instant::now();
        check = check && (val0.add(&val1) == current_sum);
        if !check {
            verifier_time += verifier_timer.elapsed();
            println!("Verifier rejects");
            println!("Prover time: {:.2?}", prover_time);
            println!("Verifier time: {:.2?}", verifier_time);
            return;
        }
        let challenge: Fr = Fr::rand(&mut rng);
        println!("Verifier's challenge: {:?}", &challenge);
        challenges.push(challenge);
        let c = val1.add(&valm1).sub(Fr::from(2u64).mul(&val0)).div(Fr::from(2u64));
        let d = val2.sub(&val1).add(&valm1).sub(&val0).sub(Fr::from(4u64).mul(&c)).div(Fr::from(6u64));
        let b = val1.sub(&val0).sub(&c).sub(&d);
        let mut temp = challenge.clone();
        current_sum = val0;
        current_sum += b.mul(&temp);
        temp *= &challenge;
        current_sum += c.mul(&temp);
        current_sum += d.mul(temp.mul(&challenge));
        verifier_time += verifier_timer.elapsed();

        prover_timer = Instant::now();
        let mc = Fr::ONE.sub(&challenge);
        for i in 0..len {
            helper1[i] = mc.mul(&helper1[i]).add(challenge.mul(&helper1[i + len]));
            helper2[i] = mc.mul(&helper2[i]).add(challenge.mul(&helper2[i + len]));
            helper3[i] = mc.mul(&helper3[i]).add(challenge.mul(&helper3[i + len]));
        }
        prover_time += prover_timer.elapsed();
    }

    //evaluate g, f at the random point
    prover_timer = Instant::now();
    let witness1 = create_witness(&g, n, &challenges);
    let witness2 = create_witness(&f, n, &challenges);

    println!("Evaluation of g, f: {:?}\n{:?}\nWitness: {:?}\n{:?}", &helper2[0], &helper3[0], &witness1, &witness2);
    prover_time += prover_timer.elapsed();

    verifier_timer = Instant::now();
    check = check && verify_evaluation(&g, n, &challenges, &helper2[0])
        && verify_evaluation(&f, n, &challenges, &helper3[0]);
    let mut eq_val = Fr::ONE;
    for i in 0..log_n {
        eq_val *= Fr::ONE.sub(&challenges[i]).sub(&rr[i]).add(Fr::from(2u64).mul(&challenges[i]).mul(&rr[i]));
    }
    eq_val = helper1[0].clone();
    check = check && (eq_val.mul(&helper2[0]).mul(beta.add(&helper3[0])) == current_sum);
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

//A dummy PCS
fn commit(g: &[Fr], n: usize) -> G1 {
    return G1::generator();
}

fn create_witness(g: &[Fr], n: usize, r: &[Fr]) -> G1 {
    return G1::generator();
}

fn verify_evaluation(g: &[Fr], n: usize, r: &[Fr], val: &Fr) -> bool {
    return true;
}