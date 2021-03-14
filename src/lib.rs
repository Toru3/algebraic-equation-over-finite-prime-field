#![no_std]
/// calcurate Jacobi symbol
///
/// Requires: `a` is positive integer. `m` is positive odd integer.
/// ```
/// use algebraic_equation_over_finite_prime_field::jacobi_symbol;
/// assert_eq!(jacobi_symbol(5, 21), 1i8);
/// assert_eq!(jacobi_symbol(7, 15), -1i8);
/// assert_eq!(jacobi_symbol(12, 27), 0i8);
/// assert_eq!(jacobi_symbol(1001, 9907), -1i8);
/// assert_eq!(jacobi_symbol(12345, 331), -1i8);
/// ```
pub fn jacobi_symbol<T>(mut a: T, mut m: T) -> i8
where
    T: Eq
        + num_traits::Zero
        + num_traits::One
        + for<'x> core::ops::DivAssign<&'x T>
        + for<'x> core::ops::RemAssign<&'x T>
        + From<i32>,
    for<'x> &'x T: core::ops::Rem<Output = T>,
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
    T: Eq + num_traits::Zero + num_traits::One + for<'x> core::ops::DivAssign<&'x T> + From<i32>,
    for<'x> &'x T: core::ops::Mul<Output = T> + core::ops::Rem<Output = T>,
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
    assert_eq!(powmod(&2, 2, &5), 4);
    assert_eq!(powmod(&3, 2, &5), 4);
    assert_eq!(powmod(&7, 4, &13), 9);
    assert_eq!(powmod(&8, 7, &19), 8);
    assert_eq!(powmod(&6, 5, &13), 2);
    assert_eq!(powmod(&31, 78, &79), 1);
    assert_eq!(powmod(&31, 82, &83), 1);
    assert_eq!(powmod(&31, 88, &89), 1);
    assert_eq!(powmod(&31, 96, &97), 1);
}

fn get_quadratic_nonresidue<T>(p: &T, f: impl Fn(T) -> T) -> T
where
    T: Clone
        + Eq
        + num_traits::Zero
        + num_traits::One
        + for<'x> core::ops::DivAssign<&'x T>
        + for<'x> core::ops::RemAssign<&'x T>
        + From<i32>
        + core::convert::TryInto<i32>,
    for<'x> &'x T: core::ops::Rem<Output = T>,
{
    use rand::distributions::Distribution;
    let mut rng = rand::thread_rng();
    let upper = if let Ok(q) = p.clone().try_into() {
        q
    } else {
        i32::MAX
    };
    let dist = rand::distributions::Uniform::new(0, upper);
    loop {
        let d = dist.sample(&mut rng);
        let d = f(T::from(d));
        if jacobi_symbol(d.clone(), p.clone()) == -1 {
            return d;
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
        assert_eq!(jacobi_symbol(get_quadratic_nonresidue(&p, |x| x), p), -1);
    }
}

fn p2_mul<T>(lhs: &(T, T), rhs: &(T, T), omega: &T, prime: &T) -> (T, T)
where
    for<'x> &'x T:
        core::ops::Add<Output = T> + core::ops::Mul<Output = T> + core::ops::Rem<Output = T>,
{
    let r0 = &(&lhs.0 * &rhs.0) + &(&(&lhs.1 * &rhs.1) * omega);
    let r1 = &(&lhs.0 * &rhs.1) + &(&lhs.1 * &rhs.0);
    (&r0 % prime, &r1 % prime)
}

fn p2_pow<T>(a: &(T, T), mut s: T, omega: &T, prime: &T) -> (T, T)
where
    T: Eq + num_traits::Zero + num_traits::One + for<'x> core::ops::DivAssign<&'x T> + From<i32>,
    for<'x> &'x T:
        core::ops::Add<Output = T> + core::ops::Mul<Output = T> + core::ops::Rem<Output = T>,
{
    let c2 = T::from(2);
    let mut x = (T::one(), T::zero());
    let mut y = (&a.0 % prime, &a.1 % prime);
    while !s.is_zero() {
        if (&s % &c2).is_one() {
            x = p2_mul(&x, &y, omega, prime);
        }
        y = p2_mul(&y, &y, omega, prime);
        s /= &c2;
    }
    x
}

fn sqrt_over_mod_p_aux<T>(a: T, p: T) -> T
where
    T: Clone
        + Eq
        + num_traits::Zero
        + num_traits::One
        + for<'x> core::ops::DivAssign<&'x T>
        + for<'x> core::ops::RemAssign<&'x T>
        + From<i32>
        + core::convert::TryInto<i32>,
    for<'x> &'x T: core::ops::Add<Output = T>
        + core::ops::Sub<Output = T>
        + core::ops::Mul<Output = T>
        + core::ops::Div<Output = T>
        + core::ops::Rem<Output = T>,
{
    let t = get_quadratic_nonresidue(&p, |t| &(&t * &t) - &a);
    let omega = &(&(&t * &t) - &a) % &p;
    let x = (t, T::one());
    let x = p2_pow(&x, &(&p + &T::one()) / &T::from(2), &omega, &p);
    x.0
}

/// Solve x^2 ≡ a (mod p)
///
/// Requires: a is non-negative integer. p is prime.
/// If equation has at least one root, this function returns `Some(x)`. `x` is a root.
/// If equation has no root, this function returns `None`.
/// ```
/// use algebraic_equation_over_finite_prime_field::sqrt_over_mod_p;
/// // two roots
/// let x = sqrt_over_mod_p(5, 11).unwrap();
/// assert!(x == 4 || x == 7);
/// let x = sqrt_over_mod_p(2, 7).unwrap();
/// assert!(x == 3 || x == 4);
/// let x = sqrt_over_mod_p(3, 13).unwrap();
/// assert!(x == 4 || x == 9);
/// let x = sqrt_over_mod_p(8, 17).unwrap();
/// assert!(x == 5 || x == 12);
/// // one root
/// assert_eq!(sqrt_over_mod_p(0, 3), Some(0));
/// // no root
/// assert_eq!(sqrt_over_mod_p(2, 3), None);
/// ```
pub fn sqrt_over_mod_p<T>(mut a: T, p: T) -> Option<T>
where
    T: Clone
        + Eq
        + num_traits::Zero
        + num_traits::One
        + for<'x> core::ops::DivAssign<&'x T>
        + for<'x> core::ops::RemAssign<&'x T>
        + From<i32>
        + core::convert::TryInto<i32>,
    for<'x> &'x T: core::ops::Add<Output = T>
        + core::ops::Sub<Output = T>
        + core::ops::Mul<Output = T>
        + core::ops::Div<Output = T>
        + core::ops::Rem<Output = T>,
{
    let c1 = T::one();
    let c3 = T::from(3);
    let c4 = T::from(4);
    let c5 = T::from(5);
    let c7 = T::from(7);
    let c8 = T::from(8);
    a %= &p;
    if a.is_zero() || a.is_one() {
        return Some(a);
    }
    if jacobi_symbol(a.clone(), p.clone()) != 1 {
        return None;
    }
    let tmp = &p % &c8;
    let r = if tmp == c3 || tmp == c7 {
        powmod(&a, &(&p + &c1) / &c4, &p)
    } else if tmp == c5 {
        let x = powmod(&a, &(&p + &c3) / &c8, &p);
        let c = &(&x * &x) % &p;
        if (&(&c - &a) % &p).is_zero() {
            x
        } else {
            x * powmod(&T::from(2), &(&p - &c1) / &c4, &p)
        }
    } else {
        sqrt_over_mod_p_aux(a, p)
    };
    Some(r)
}
