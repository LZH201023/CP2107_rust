use ark_ff::{Field, One};
use ark_bls12_381::Fr;
use ark_std::{vec::Vec};
use std::ops::{Add, Sub, Mul};
pub fn ntt<S: Clone + Add<Output = S> + Sub<Output = S> + Mul<Fr, Output = S>>(
    f: &[S],
    n: usize,
) -> Vec<S> {
    if n == 1 {
        return vec![f[0].clone()];
    }
    
    let mut arr: Vec<S> = vec![f[0].clone(); n];
    let mut arr1 = vec![0usize; n];
    let mut t = n / 2;
    let mut h = n;
    let mut temp = 1;
    let log_n = n.ilog2() as usize;

    arr1[0] = 0;
    for _ in 0..log_n {
        for j in (0..n).step_by(h) {
            arr1[j + t] = arr1[j] + temp;
        }
        t /= 2;
        h /= 2;
        temp *= 2;
    }

    for i in 0..n {
        arr[i] = f[arr1[i]].clone();
    }

    let mut temp_arr = vec![f[0].clone(); n];
    let mut tth_root: Fr = -Fr::one();

    let mut t = 2;

    for _ in 0..log_n {
        for j in (0..n).step_by(t) {
            let mut omega: Fr = Fr::one();
            for k in 0..h {
                let u = arr[j + k].clone();
                let v = arr[j + k + h].clone() * omega.clone();
                temp_arr[k] = u.clone() + v.clone();
                temp_arr[k + h] = u - v;
                omega = omega.mul(&tth_root);
            }
            for k in 0..t {
                arr[j + k] = temp_arr[k].clone();
            }
        }
        t *= 2;
        h *= 2;
        tth_root = tth_root.sqrt().unwrap();
    }
    arr
}

pub fn intt<S: Clone + Add<Output = S> + Sub<Output = S> + Mul<Fr, Output = S>>(
    f: &[S],
    n: usize,
    ge: &Option<Fr>,
) -> Vec<S> {
    let mut INV_G: Fr = Fr::ONE;   
    let log_n = n.ilog2() as usize;
    if ge.is_none() {
        if n != 1 {
            let mut G = -Fr::ONE;
            for _ in 1..log_n {
                G = G.sqrt().unwrap();
            }
            let mut a = G.clone();
            for _ in 1..n {
                if a.eq(&Fr::ONE) {
                    println!("error");
                }
                a = a*G.clone();
            }
            INV_G = G.inverse().unwrap();
        }
    } else if n > 1 {
        INV_G = ge.and_then(|x| x.inverse()).unwrap();
    }
    let mut arr: Vec<S> = f.to_vec();
    let mut res: Vec<S> = f.to_vec();
    let mut t = n;
    let mut h = n / 2;
    let mut w: Fr = INV_G.mul(Fr::ONE);
    let half = Fr::from(2u64).inverse().unwrap();
    for _ in 0..log_n {
        for j in (0..n).step_by(t) {
            let mut a: Fr = Fr::one();
            for k in 0..h {
                res[j + k] = (arr[j + k].clone() + arr[j + k + h].clone()) * half.clone();
                res[j + k + h] = (arr[j + k].clone() - arr[j + k + h].clone()) * half.clone() * a.clone();
                a = a.mul(&w);
            }
        }
        w = w.mul(&w);
        t /= 2;
        h /= 2;
        std::mem::swap(&mut arr, &mut res);
    }
    let mut temp = vec![0usize; n];
    temp[0] = 0;
    let mut t = 1;
    h = n / 2;
    while h > 0 {
        for j in 0..t {
            temp[j + t] = temp[j] + h;
        }
        t *= 2;
        h /= 2;
    }

    for i in 0..n {
        res[i] = arr[temp[i]].clone();
    }
    
    res
}

pub fn poly_multi(f: &[Fr], df: usize, h: &[Fr], dh: usize) -> Vec<Fr> {
    let n = df + dh + 1;
    let mut N = 1;
    while N < n {
        N <<= 1;
    }

    let mut f_n = vec![Fr::ZERO; N];
    let mut h_n = vec![Fr::ZERO; N];

    f_n[..=df].copy_from_slice(&f[..=df]);
    h_n[..=dh].copy_from_slice(&h[..=dh]);

    let f_n_ntt = ntt(&f_n, N);
    let h_n_ntt = ntt(&h_n, N);

    let mut product = vec![Fr::ZERO; N];
    for i in 0..N {
        product[i] = &f_n_ntt[i] * &h_n_ntt[i];
    }

    let res = intt(&product, N, &None);
    res
}