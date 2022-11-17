use ark_ec::{AffineCurve, PairingEngine, ProjectiveCurve};
use ark_ff::{Field, One, PrimeField};
use ark_std::rand::Rng;
use ark_std::{cfg_into_iter, cfg_iter, vec, vec::Vec, UniformRand};

#[cfg(feature = "parallel")]
use rayon::prelude::*;

#[derive(Debug, Clone)]
pub struct PairingCheck<E: PairingEngine> {
    pub left: E::Fqk,
    pub right: E::Fqk,
    pub r: E::Fr,
    pub current_r: E::Fr,
    pending: Vec<(E::G1Prepared, E::G2Prepared)>,
}

impl<E> PairingCheck<E>
where
    E: PairingEngine,
{
    pub fn new_using_rng<R: Rng>(rng: &mut R) -> Self {
        Self::new(E::Fr::rand(rng))
    }

    pub fn new(r: E::Fr) -> Self {
        Self {
            left: E::Fqk::one(),
            right: E::Fqk::one(),
            r,
            current_r: E::Fr::one(),
            pending: vec![],
        }
    }

    pub fn add_sources_and_target(
        &mut self,
        a: &[E::G1Affine],
        b: &[E::G2Affine],
        out: &E::Fqk,
        lazy: bool,
    ) {
        assert_eq!(a.len(), b.len());

        let m = self.current_r.into_repr();
        let mut it = cfg_iter!(a)
            .zip(cfg_iter!(b))
            .map(|(a, b)| {
                (
                    E::G1Prepared::from(a.mul(m).into_affine()),
                    E::G2Prepared::from(*b),
                )
            })
            .collect::<Vec<_>>();
        if lazy {
            self.pending.append(&mut it);
        } else {
            self.left *= E::miller_loop(it.iter());
        }
        self.right *= out.pow(m);
        self.current_r *= self.r;
    }

    pub fn add_sources(
        &mut self,
        a: &[E::G1Affine],
        b: &[E::G2Affine],
        c: &[E::G1Affine],
        d: &[E::G2Affine],
        lazy: bool,
    ) {
        assert_eq!(a.len(), b.len());
        assert_eq!(c.len(), d.len());
        let m = self.current_r.into_repr();
        let mut it = cfg_iter!(a)
            .zip(cfg_iter!(b))
            .map(|(a, b)| {
                (
                    E::G1Prepared::from(a.mul(m).into_affine()),
                    E::G2Prepared::from(*b),
                )
            })
            .collect::<Vec<_>>();
        let mut it1 = cfg_iter!(c)
            .zip(cfg_iter!(d))
            .map(|(c, d)| {
                (
                    E::G1Prepared::from(-c.mul(m).into_affine()),
                    E::G2Prepared::from(*d),
                )
            })
            .collect::<Vec<_>>();
        if lazy {
            self.pending.append(&mut it);
            self.pending.append(&mut it1);
        } else {
            self.left *= E::miller_loop(it.iter().chain(it1.iter()));
        }
        self.current_r *= self.r;
    }

    pub fn add_prepared_sources_and_target(
        &mut self,
        a: &[E::G1Affine],
        b: Vec<E::G2Prepared>,
        out: &E::Fqk,
        lazy: bool,
    ) {
        assert_eq!(a.len(), b.len());
        let m = self.current_r.into_repr();
        let mut it = cfg_iter!(a)
            .map(|a| E::G1Prepared::from(a.mul(m).into_affine()))
            .zip(cfg_into_iter!(b))
            .collect::<Vec<_>>();
        if lazy {
            self.pending.append(&mut it);
        } else {
            self.left *= E::miller_loop(it.iter());
        }
        self.right *= out.pow(m);
        self.current_r *= self.r;
    }

    pub fn verify(&self) -> bool {
        let mut p = E::Fqk::one();
        if self.pending.len() > 0 {
            p = E::miller_loop(self.pending.iter());
        }
        let left = self.left * p;
        E::final_exponentiation(&left).unwrap() == self.right
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use ark_bls12_381::{Bls12_381, G1Projective, G2Projective};
    use ark_ec::bls12::{G1Prepared, G2Prepared};
    use ark_std::rand::prelude::StdRng;
    use ark_std::rand::SeedableRng;
    use ark_std::UniformRand;
    use std::time::Instant;

    fn rev_vec<T: Clone>(v: &[T]) -> Vec<T> {
        let mut x = v.to_vec();
        x.reverse();
        x
    }

    #[test]
    fn test_pairing_randomize() {
        fn check(lazy: bool) {
            let mut rng = StdRng::seed_from_u64(0u64);
            let n = 10;
            let mut t1 = 0;

            let checker_type = if lazy { "lazy-checker" } else { "checker" };

            let a1 = (0..n)
                .map(|_| G1Projective::rand(&mut rng).into_affine())
                .collect::<Vec<_>>();
            let b1 = (0..n)
                .map(|_| G2Projective::rand(&mut rng).into_affine())
                .collect::<Vec<_>>();
            let a2 = (0..n + 5)
                .map(|_| G1Projective::rand(&mut rng).into_affine())
                .collect::<Vec<_>>();
            let b2 = (0..n + 5)
                .map(|_| G2Projective::rand(&mut rng).into_affine())
                .collect::<Vec<_>>();
            let a3 = (0..n - 2)
                .map(|_| G1Projective::rand(&mut rng).into_affine())
                .collect::<Vec<_>>();
            let b3 = (0..n - 2)
                .map(|_| G2Projective::rand(&mut rng).into_affine())
                .collect::<Vec<_>>();

            let start = Instant::now();
            let out1 = Bls12_381::product_of_pairings(
                &a1.iter()
                    .zip(b1.iter())
                    .map(|(a, b)| (G1Prepared::from(*a), G2Prepared::from(*b)))
                    .collect::<Vec<_>>(),
            );
            t1 += start.elapsed().as_micros();

            let start = Instant::now();
            let out2 = Bls12_381::product_of_pairings(
                &a2.iter()
                    .zip(b2.iter())
                    .map(|(a, b)| (G1Prepared::from(*a), G2Prepared::from(*b)))
                    .collect::<Vec<_>>(),
            );
            t1 += start.elapsed().as_micros();

            let start = Instant::now();
            let out3 = Bls12_381::product_of_pairings(
                &a3.iter()
                    .zip(b3.iter())
                    .map(|(a, b)| (G1Prepared::from(*a), G2Prepared::from(*b)))
                    .collect::<Vec<_>>(),
            );
            t1 += start.elapsed().as_micros();

            let start = Instant::now();
            let mut checker = PairingCheck::<Bls12_381>::new_using_rng(&mut rng);
            checker.add_sources_and_target(&a1, &b1, &out1, lazy);
            checker.add_sources_and_target(&a2, &b2, &out2, lazy);
            checker.add_sources_and_target(&a3, &b3, &out3, lazy);
            assert!(checker.verify());
            println!(
                "Time taken with {}: {} us",
                checker_type,
                start.elapsed().as_micros()
            );
            println!("Time taken without checker {} us", t1);

            let mut checker = PairingCheck::<Bls12_381>::new_using_rng(&mut rng);
            checker.add_sources(&a1, &b1, &rev_vec(&a1), &rev_vec(&b1), lazy);
            checker.add_sources(&a2, &b2, &rev_vec(&a2), &rev_vec(&b2), lazy);
            checker.add_sources(&a3, &b3, &rev_vec(&a3), &rev_vec(&b3), lazy);
            assert!(checker.verify());

            let start = Instant::now();
            let mut checker = PairingCheck::<Bls12_381>::new_using_rng(&mut rng);
            checker.add_sources_and_target(&a1, &b1, &out1, lazy);
            checker.add_sources_and_target(&a2, &b2, &out2, lazy);
            checker.add_sources_and_target(&a3, &b3, &out3, lazy);
            checker.add_sources(&a1, &b1, &rev_vec(&a1), &rev_vec(&b1), lazy);
            checker.add_sources(&a2, &b2, &rev_vec(&a2), &rev_vec(&b2), lazy);
            checker.add_sources(&a3, &b3, &rev_vec(&a3), &rev_vec(&b3), lazy);
            assert!(checker.verify());
            println!(
                "Time taken with {}: {} us",
                checker_type,
                start.elapsed().as_micros()
            );

            // Mix lazy and instant
            let mut checker = PairingCheck::<Bls12_381>::new_using_rng(&mut rng);
            checker.add_sources_and_target(&a1, &b1, &out1, lazy);
            checker.add_sources_and_target(&a2, &b2, &out2, !lazy);
            checker.add_sources_and_target(&a3, &b3, &out3, lazy);
            checker.add_sources(&a1, &b1, &rev_vec(&a1), &rev_vec(&b1), lazy);
            checker.add_sources(&a2, &b2, &rev_vec(&a2), &rev_vec(&b2), !lazy);
            checker.add_sources(&a3, &b3, &rev_vec(&a3), &rev_vec(&b3), !lazy);
            assert!(checker.verify());
        }
        check(false);
        check(true);
    }
}
