//! Find roots of polynomial in modulo prime.
//! ```
//! use algebraic_equation_over_finite_prime_field::{find_all_roots_over_mod_p, PolynomialOverP};
//! // (x^2+2)(x-1)(x-3)≡x^4+x^3+2x+1 (mod 5)
//! let p = PolynomialOverP::<i32>::new(vec![1, 2, 0, 1, 1], 5);
//! let mut v = find_all_roots_over_mod_p::<i32>(p);
//! v.sort();
//! assert_eq!(vec![1, 3], v);
//! ```

#![cfg_attr(feature = "__internal_inject_debug", recursion_limit = "16")]
mod sealed {
    pub trait SizedExt: std::marker::Sized + std::fmt::Debug + std::fmt::Display {}
    impl<T> SizedExt for T where T: std::marker::Sized + std::fmt::Debug + std::fmt::Display {}
    #[cfg(not(feature = "__internal_inject_debug"))]
    pub use std::marker::Sized;
    #[cfg(feature = "__internal_inject_debug")]
    pub use SizedExt as Sized;
}
use num_traits::{One, Zero};
pub use polynomial_over_finite_prime_field::PolynomialOverP;
use rand::distributions::uniform::SampleUniform;
pub use ring_algorithm::RingNormalize;
use sealed::Sized;
use std::convert::TryFrom;
use std::ops::{
    Add, AddAssign, BitAnd, Div, DivAssign, Mul, Neg, Rem, RemAssign, ShrAssign, Sub, SubAssign,
};

/// calcurate Jacobi symbol
///
/// Requires: `a` is positive integer. `m` is positive odd integer.
/// ```
/// use algebraic_equation_over_finite_prime_field::jacobi_symbol;
/// assert_eq!(jacobi_symbol::<i32>(5, 21), 1i8);
/// assert_eq!(jacobi_symbol::<i32>(7, 15), -1i8);
/// assert_eq!(jacobi_symbol::<i32>(12, 27), 0i8);
/// assert_eq!(jacobi_symbol::<i32>(1001, 9907), -1i8);
/// assert_eq!(jacobi_symbol::<i32>(12345, 331), -1i8);
/// ```
pub fn jacobi_symbol<T>(mut a: T, mut m: T) -> i8
where
    T: Sized + Eq + Zero + One + for<'x> DivAssign<&'x T> + for<'x> RemAssign<&'x T> + From<u8>,
    for<'x> &'x T: Rem<Output = T>,
{
    let c2 = T::from(2);
    let c3 = T::from(3);
    let c4 = T::from(4);
    let c5 = T::from(5);
    let c8 = T::from(8);
    assert!(!(&m % &c2).is_zero());
    a %= &m;
    let mut t = 1i8;
    while !a.is_zero() {
        // (2/p) = (-1)^{(p^2-1)/8}
        while (&a % &c2).is_zero() {
            a /= &c2;
            let tmp = &m % &c8;
            if tmp == c3 || tmp == c5 {
                t = -t;
            }
        }
        // quadratic reciprocity
        core::mem::swap(&mut a, &mut m);
        if &a % &c4 == c3 && &m % &c4 == c3 {
            t = -t;
        }
        a %= &m;
    }
    if m.is_one() {
        t
    } else {
        0
    }
}

fn powmod<T>(a: &T, mut p: T, modulo: &T) -> T
where
    T: Sized + Eq + Zero + One + for<'x> DivAssign<&'x T> + From<u8>,
    for<'x> &'x T: Mul<Output = T> + Rem<Output = T>,
{
    let c2 = T::from(2);
    let mut x = T::one();
    let mut y = a % modulo;
    while !p.is_zero() {
        if (&p % &c2).is_one() {
            x = &(&x * &y) % modulo;
        }
        y = &(&y * &y) % modulo;
        p /= &c2;
    }
    x
}

#[test]
fn powmod_test() {
    assert_eq!(powmod::<i32>(&2, 2, &5), 4);
    assert_eq!(powmod::<i32>(&3, 2, &5), 4);
    assert_eq!(powmod::<i32>(&7, 4, &13), 9);
    assert_eq!(powmod::<i32>(&8, 7, &19), 8);
    assert_eq!(powmod::<i32>(&6, 5, &13), 2);
    assert_eq!(powmod::<i32>(&31, 78, &79), 1);
    assert_eq!(powmod::<i32>(&31, 82, &83), 1);
    assert_eq!(powmod::<i32>(&31, 88, &89), 1);
    assert_eq!(powmod::<i32>(&31, 96, &97), 1);
}

fn get_quadratic_nonresidue<T, F: Fn(T) -> T>(p: &T, f: F) -> (T, T)
where
    T: Sized
        + Clone
        + Eq
        + Zero
        + One
        + for<'x> DivAssign<&'x T>
        + for<'x> RemAssign<&'x T>
        + From<u8>
        + SampleUniform,
    for<'x> &'x T: Rem<Output = T>,
{
    use rand::distributions::Distribution;
    let mut rng = rand::thread_rng();
    let dist = rand::distributions::Uniform::new(T::zero(), p);
    loop {
        let d = dist.sample(&mut rng);
        let e = f(d.clone());
        if jacobi_symbol::<T>(e.clone(), p.clone()) == -1 {
            return (d, e);
        }
    }
}

#[test]
fn get_quadratic_nonresidue_test() {
    let v = [
        3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97,
        2617, 2621, 2633, 2647, 2657,
    ];
    for &p in v.iter() {
        assert_eq!(
            jacobi_symbol::<i32>(get_quadratic_nonresidue::<i32, _>(&p, |x| x).0, p),
            -1
        );
    }
}

fn p2_mul<T>(lhs: &(T, T), rhs: &(T, T), omega: &T, prime: &T) -> (T, T)
where
    T: Sized,
    for<'x> &'x T: Add<Output = T> + Mul<Output = T> + Rem<Output = T>,
{
    let r0 = &(&lhs.0 * &rhs.0) + &(&(&(&lhs.1 * &rhs.1) % prime) * omega);
    let r1 = &(&lhs.0 * &rhs.1) + &(&lhs.1 * &rhs.0);
    (&r0 % prime, &r1 % prime)
}

fn p2_pow<T>(a: &(T, T), mut s: T, omega: &T, prime: &T) -> (T, T)
where
    T: Sized + Eq + Zero + One + for<'x> DivAssign<&'x T> + From<u8>,
    for<'x> &'x T: Add<Output = T> + Mul<Output = T> + Rem<Output = T>,
{
    let c2 = T::from(2);
    let mut x = (T::one(), T::zero());
    let mut y = (&a.0 % prime, &a.1 % prime);
    while !s.is_zero() {
        if (&s % &c2).is_one() {
            x = p2_mul::<T>(&x, &y, omega, prime);
        }
        y = p2_mul::<T>(&y, &y, omega, prime);
        s /= &c2;
    }
    x
}

fn sqrt_over_mod_p_aux<T>(a: T, p: &T) -> T
where
    T: Sized
        + Clone
        + Eq
        + Zero
        + One
        + for<'x> DivAssign<&'x T>
        + for<'x> RemAssign<&'x T>
        + From<u8>
        + SampleUniform,
    for<'x> &'x T:
        Add<Output = T> + Sub<Output = T> + Mul<Output = T> + Div<Output = T> + Rem<Output = T>,
{
    let (t, omega) = get_quadratic_nonresidue::<T, _>(p, |t| &(&(&t * &t) + &(p - &a)) % p);
    let x = (t, T::one());
    let x = p2_pow::<T>(&x, &(p + &T::one()) / &T::from(2), &omega, p);
    x.0
}

/// Solve: $`x^2 ≡ a \pmod p`$
///
/// Requires: a is non-negative integer. p is prime.
/// If equation has at least one root, this function returns `Some(x)`. `x` is a root.
/// If equation has no root, this function returns `None`.
/// ```
/// use algebraic_equation_over_finite_prime_field::sqrt_over_mod_p;
/// // two roots
/// let x = sqrt_over_mod_p::<i32>(5, &11).unwrap();
/// assert!(x == 4 || x == 7);
/// let x = sqrt_over_mod_p::<i32>(2, &7).unwrap();
/// assert!(x == 3 || x == 4);
/// let x = sqrt_over_mod_p::<i32>(3, &13).unwrap();
/// assert!(x == 4 || x == 9);
/// let x = sqrt_over_mod_p::<i32>(8, &17).unwrap();
/// assert!(x == 5 || x == 12);
/// // one root
/// assert_eq!(sqrt_over_mod_p::<i32>(0, &3), Some(0));
/// // no root
/// assert_eq!(sqrt_over_mod_p::<i32>(2, &3), None);
/// ```
pub fn sqrt_over_mod_p<T>(mut a: T, p: &T) -> Option<T>
where
    T: Sized
        + Clone
        + Eq
        + Zero
        + One
        + for<'x> DivAssign<&'x T>
        + for<'x> RemAssign<&'x T>
        + From<u8>
        + SampleUniform,
    for<'x> &'x T:
        Add<Output = T> + Sub<Output = T> + Mul<Output = T> + Div<Output = T> + Rem<Output = T>,
{
    let c1 = T::one();
    let c3 = T::from(3);
    let c4 = T::from(4);
    let c5 = T::from(5);
    let c7 = T::from(7);
    let c8 = T::from(8);
    a %= p;
    if a.is_zero() || a.is_one() {
        return Some(a);
    }
    if jacobi_symbol::<T>(a.clone(), p.clone()) != 1 {
        return None;
    }
    let tmp = p % &c8;
    let r = if tmp == c3 || tmp == c7 {
        // easy pattern 1
        powmod::<T>(&a, &(p + &c1) / &c4, p)
    } else if tmp == c5 {
        // easy pattern 2
        let x = powmod::<T>(&a, &(p + &c3) / &c8, p);
        if &(&x * &x) % p == a {
            x
        } else {
            &(x * powmod::<T>(&T::from(2), &(p - &c1) / &c4, p)) % p
        }
    } else {
        // hard pattern
        sqrt_over_mod_p_aux::<T>(a, p)
    };
    Some(r)
}

#[test]
fn sqrt_test() {
    use rand::distributions::{Distribution, Uniform};
    use rand::prelude::*;
    let mut rng = rand::thread_rng();
    for _ in 0..100_000 {
        let p = rng.gen::<i32>().abs() as i64;
        if !primal::is_prime(p as u64) {
            continue;
        }
        let between = Uniform::from(0..p);
        for _ in 0..100 {
            let a = between.sample(&mut rng);
            dbg!((a, p));
            let x = sqrt_over_mod_p::<i64>(a, &p);
            if let Some(x) = x {
                assert!(0 <= x && x < p);
                assert_eq!(x * x % p, a);
            } else {
                assert_eq!(jacobi_symbol::<i64>(a, p), -1);
            }
        }
    }
}

/// Solve: $`ax + b ≡ 0 \pmod p`$
pub fn solve_liner_equation<T>(a: T, b: T, p: T) -> T
where
    T: Sized + Clone + Eq + Ord + Zero + One + RingNormalize,
    for<'x> &'x T: ring_algorithm::EuclideanRingOperation<T>,
{
    let x = ring_algorithm::modulo_division::<T>(&p - &b, a, p.clone()).unwrap();
    if x < T::zero() {
        x + p
    } else {
        x
    }
}

#[test]
fn liner_test() {
    use rand::distributions::{Distribution, Uniform};
    use rand::prelude::*;
    let mut rng = rand::thread_rng();
    for _ in 0..100_000 {
        let p = rng.gen::<i32>().abs() as i64;
        if !primal::is_prime(p as u64) {
            continue;
        }
        let between1 = Uniform::from(1..p);
        let between2 = Uniform::from(0..p);
        for _ in 0..100 {
            let a = between1.sample(&mut rng);
            let b = between2.sample(&mut rng);
            dbg!((a, p));
            let x = solve_liner_equation::<i64>(a, b, p);
            dbg!(x);
            assert!(0 <= x && x < p);
            assert_eq!((a * x + b) % p, 0);
        }
    }
}

/// Solve: $`ax^2 + bx + c ≡ 0 \pmod p`$
///
/// Requires: $`p`$: odd prime, $`\left(\frac{D}{p}\right)=1`$ where $`D=b^2-4ac`$.
pub fn solve_quadratic_equation<T>(a: T, b: T, c: T, p: T) -> (T, T)
where
    T: Sized
        + Clone
        + Eq
        + Ord
        + Zero
        + One
        + RingNormalize
        + for<'x> DivAssign<&'x T>
        + for<'x> RemAssign<&'x T>
        + Neg<Output = T>
        + From<u8>
        + SampleUniform,
    for<'x> &'x T: Add<Output = T>
        + Sub<Output = T>
        + Mul<Output = T>
        + Div<Output = T>
        + Rem<Output = T>
        + ring_algorithm::EuclideanRingOperation<T>,
{
    let c2 = T::from(2);
    let c4 = T::from(4);
    let b2 = &(&b * &b) % &p;
    let ac4 = &(&(&(&a * &c) % &p) * &c4) % &p;
    let det = &(&b2 - &ac4) % &p;
    let det = if det < T::zero() { &det + &p } else { det };
    let sd1 = sqrt_over_mod_p::<T>(det, &p).unwrap();
    let sd2 = &p - &sd1;
    let inv_a = ring_algorithm::modulo_inverse::<T>(&a * &c2, p.clone()).unwrap();
    let r1 = &(&(&sd1 - &b) * &inv_a) % &p;
    let r1 = if r1 < T::zero() { &r1 + &p } else { r1 };
    let r2 = &(&(&sd2 - &b) * &inv_a) % &p;
    let r2 = if r2 < T::zero() { &r2 + &p } else { r2 };
    (r1, r2)
}

#[test]
fn quadratic_test() {
    use rand::distributions::{Distribution, Uniform};
    use rand::prelude::*;
    let mut rng = rand::thread_rng();
    for _ in 0..100_000 {
        let prime = (rng.gen::<i32>() as i64).abs();
        if prime == 2 || !primal::is_prime(prime as u64) {
            continue;
        }
        let between1 = Uniform::from(1..prime);
        let between2 = Uniform::from(0..prime);
        for _ in 0..100 {
            let a = between1.sample(&mut rng);
            let b = between2.sample(&mut rng);
            let c = between2.sample(&mut rng);
            let d = b * b + prime - (4 * a % prime * c % prime);
            dbg!((d, prime));
            if jacobi_symbol::<i64>(d, prime) == 1 {
                dbg!((a, b, c, prime));
                let (x1, x2) = solve_quadratic_equation::<i64>(a, b, c, prime);
                dbg!((x1, x2));
                assert!(0 <= x1 && x1 < prime);
                assert!(0 <= x2 && x2 < prime);
                assert_eq!(((a * x1 + b) % prime * x1 + c) % prime, 0);
                assert_eq!(((a * x2 + b) % prime * x2 + c) % prime, 0);
            }
        }
    }
}

fn decompose<T>(g: PolynomialOverP<T>, prime: T) -> (PolynomialOverP<T>, PolynomialOverP<T>)
where
    T: Sized
        + Clone
        + Eq
        + Ord
        + Zero
        + One
        + for<'x> AddAssign<&'x T>
        + for<'x> SubAssign<&'x T>
        + for<'x> DivAssign<&'x T>
        + for<'x> RemAssign<&'x T>
        + From<u8>
        + SampleUniform
        + ShrAssign<u8>
        + for<'x> SubAssign<&'x T>
        + RingNormalize,
    for<'x> &'x T: Add<Output = T>
        + Neg<Output = T>
        + Sub<Output = T>
        + Mul<Output = T>
        + Div<Output = T>
        + Rem<Output = T>
        + BitAnd<Output = T>,
{
    use rand::distributions::Distribution;
    let c2 = T::from(2);
    let mut rng = rand::thread_rng();
    let dist = rand::distributions::Uniform::new(T::zero(), prime.clone());
    let one = PolynomialOverP::one(prime.clone());
    loop {
        let a = dist.sample(&mut rng);
        let xpa = PolynomialOverP::<T>::new(vec![a, T::one()], prime.clone());
        let xpa_pow = &modulo_n_tools::mul_pow_mod::<PolynomialOverP<T>, T>(
            one.clone(),
            xpa,
            &(&prime - &T::one()) / &c2,
            &g,
        ) - &one;
        let h = ring_algorithm::gcd::<PolynomialOverP<T>>(xpa_pow, g.clone());
        if let Some(deg) = h.deg() {
            if 0 < deg && deg < g.deg().unwrap() {
                let i = &g / &h;
                return (h, i);
            }
        }
    }
}

fn find_roots<T>(poly: PolynomialOverP<T>, prime: T, roots: &mut Vec<T>)
where
    T: Sized
        + Clone
        + Eq
        + Ord
        + Zero
        + One
        + for<'x> AddAssign<&'x T>
        + for<'x> SubAssign<&'x T>
        + for<'x> DivAssign<&'x T>
        + for<'x> RemAssign<&'x T>
        + Neg<Output = T>
        + From<u8>
        + SampleUniform
        + ShrAssign<u8>
        + for<'x> SubAssign<&'x T>
        + RingNormalize,
    for<'x> &'x T: Add<Output = T>
        + Neg<Output = T>
        + Sub<Output = T>
        + Mul<Output = T>
        + Div<Output = T>
        + Rem<Output = T>
        + BitAnd<Output = T>,
{
    match poly.deg() {
        None => unreachable!(),
        Some(0) => unreachable!(),
        Some(1) => {
            let mut coef = poly.coefs();
            let a = coef.pop().unwrap();
            let b = coef.pop().unwrap();
            let r = solve_liner_equation::<T>(a, b, prime);
            roots.push(r);
        }
        Some(2) => {
            let mut coef = poly.coefs();
            let a = coef.pop().unwrap();
            let b = coef.pop().unwrap();
            let c = coef.pop().unwrap();
            let (r1, r2) = solve_quadratic_equation::<T>(a, b, c, prime);
            roots.push(r1);
            roots.push(r2);
        }
        Some(_) => {
            let (f, g) = decompose::<T>(poly, prime.clone());
            find_roots::<T>(f, prime.clone(), roots);
            find_roots::<T>(g, prime, roots);
        }
    }
}

/// Find all roots of polynomial in modulo prime.
///
/// This function do **not** brute-force search or factorize polynomial.
/// ```
/// use algebraic_equation_over_finite_prime_field::{find_all_roots_over_mod_p, PolynomialOverP};
/// // (x^2+2)(x-1)(x-3)≡x^4+x^3+2x+1 (mod 5)
/// let p = PolynomialOverP::<i32>::new(vec![1, 2, 0, 1, 1], 5);
/// let mut v = find_all_roots_over_mod_p::<i32>(p);
/// v.sort();
/// assert_eq!(vec![1, 3], v);
/// ```
pub fn find_all_roots_over_mod_p<T>(poly: PolynomialOverP<T>) -> Vec<T>
where
    usize: std::convert::TryFrom<T>,
    <usize as std::convert::TryFrom<T>>::Error: std::fmt::Debug,
    T: Sized
        + Clone
        + Eq
        + Ord
        + Zero
        + One
        + for<'x> AddAssign<&'x T>
        + for<'x> SubAssign<&'x T>
        + for<'x> DivAssign<&'x T>
        + for<'x> RemAssign<&'x T>
        + Neg<Output = T>
        + From<u8>
        + SampleUniform
        + ShrAssign<u8>
        + for<'x> SubAssign<&'x T>
        + RingNormalize,
    for<'x> &'x T: Add<Output = T>
        + Neg<Output = T>
        + Sub<Output = T>
        + Mul<Output = T>
        + Div<Output = T>
        + Rem<Output = T>
        + BitAnd<Output = T>,
{
    let prime = poly.prime_ref().clone();
    let xpmx = PolynomialOverP::from_monomial(
        T::one(),
        usize::try_from(prime.clone()).unwrap(),
        prime.clone(),
    ) - PolynomialOverP::from_monomial(T::one(), 1, prime.clone());
    let mut g = ring_algorithm::gcd::<PolynomialOverP<T>>(poly, xpmx);
    let mut roots = Vec::new();
    if g.eval(&T::zero()).is_zero() {
        roots.push(T::zero());
        g /= PolynomialOverP::from_monomial(T::one(), 1, prime.clone());
    }
    let gd = g.deg().unwrap();
    if gd > 0 {
        find_roots::<T>(g, prime, &mut roots);
    }
    roots
}

#[test]
fn find_all_roots_over_mod_p_test_small() {
    let p = PolynomialOverP::<i32>::new(vec![-1, 0, 0, 0, 1], 5);
    let mut v = find_all_roots_over_mod_p::<i32>(p);
    v.sort_unstable();
    assert_eq!(vec![1, 2, 3, 4], v);
}

#[cfg(test)]
fn find_all_roots_over_mod_p_test_aux(p: i32, rng: &mut rand::rngs::ThreadRng) {
    use rand::distributions::Distribution;
    use rayon::prelude::*;
    let dist_coef = rand::distributions::Uniform::new(0i32, p);
    for _ in 0..100 {
        let mut v = Vec::with_capacity(100);
        for _ in 0..100 {
            let c = dist_coef.sample(rng);
            v.push(c);
        }
        let f = PolynomialOverP::<i32>::new(v, p);
        //dbg!(&f);
        let brute_force = (0..p)
            .into_par_iter()
            .filter(|i| f.eval(i).is_zero())
            .collect::<Vec<_>>();
        let mut ans = find_all_roots_over_mod_p::<i32>(f);
        ans.sort_unstable();
        assert_eq!(ans, brute_force);
    }
}

#[test]
fn find_all_roots_over_mod_p_test() {
    use rand::distributions::Distribution;
    let mut rng = rand::thread_rng();
    let dist_prime = rand::distributions::Uniform::new(2i32, 1000);
    for _ in 0..100 {
        let p = dist_prime.sample(&mut rng);
        if !primal::is_prime(p as u64) {
            continue;
        }
        find_all_roots_over_mod_p_test_aux(p, &mut rng);
    }
}
