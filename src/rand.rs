use rand::distr::uniform::SampleBorrow;
use rand::distr::uniform::SampleUniform;
use rand::distr::uniform::UniformInt;
use rand::distr::uniform::UniformSampler;
use rand::distr::Distribution;
use rand::distr::StandardUniform;
use rand::Rng;

use crate::Duration;
use crate::Time;

impl Distribution<Time> for StandardUniform {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Time {
        Time(rng.random())
    }
}

#[derive(Debug, Clone, Copy)]
pub struct UniformTime(UniformInt<i64>);

impl UniformSampler for UniformTime {
    type X = Time;

    fn new<B1, B2>(low: B1, high: B2) -> Result<Self, rand::distr::uniform::Error>
    where
        B1: SampleBorrow<Self::X> + Sized,
        B2: SampleBorrow<Self::X> + Sized,
    {
        UniformInt::new(low.borrow().0, high.borrow().0).map(Self)
    }

    fn new_inclusive<B1, B2>(low: B1, high: B2) -> Result<Self, rand::distr::uniform::Error>
    where
        B1: SampleBorrow<Self::X> + Sized,
        B2: SampleBorrow<Self::X> + Sized,
    {
        UniformInt::new_inclusive(low.borrow().0, high.borrow().0).map(Self)
    }

    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Self::X {
        Time(self.0.sample(rng))
    }
}

impl SampleUniform for Time {
    type Sampler = UniformTime;
}

impl Distribution<Duration> for StandardUniform {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Duration {
        Duration(rng.random())
    }
}

#[derive(Debug, Clone, Copy)]
pub struct UniformDuration(UniformInt<i64>);

impl UniformSampler for UniformDuration {
    type X = Duration;

    fn new<B1, B2>(low: B1, high: B2) -> Result<Self, rand::distr::uniform::Error>
    where
        B1: SampleBorrow<Self::X> + Sized,
        B2: SampleBorrow<Self::X> + Sized,
    {
        UniformInt::new(low.borrow().0, high.borrow().0).map(Self)
    }

    fn new_inclusive<B1, B2>(low: B1, high: B2) -> Result<Self, rand::distr::uniform::Error>
    where
        B1: SampleBorrow<Self::X> + Sized,
        B2: SampleBorrow<Self::X> + Sized,
    {
        UniformInt::new_inclusive(low.borrow().0, high.borrow().0).map(Self)
    }

    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Self::X {
        Duration(self.0.sample(rng))
    }
}

impl SampleUniform for Duration {
    type Sampler = UniformDuration;
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn standard_time() {
        let _: Time = rand::random();
        let _: Time = rand::rng().random();
    }

    #[test]
    fn uniform_time() {
        let mut rng = rand::rng();
        assert_eq!(Time::EPOCH, rng.random_range(Time::EPOCH..Time::millis(1)));
        assert_eq!(Time::EPOCH, rng.random_range(Time::EPOCH..=Time::EPOCH));

        let low = Time::millis(100);
        let high = Time::millis(110);
        for _ in 0..1000 {
            let x = rng.random_range(low..high);
            assert!((low..high).contains(&x));
        }
    }

    #[test]
    fn standard_duration() {
        let _: Duration = rand::random();
        let _: Duration = rand::rng().random();
    }

    #[test]
    fn uniform_duration() {
        let mut rng = rand::rng();
        assert_eq!(
            Duration::ZERO,
            rng.random_range(Duration::ZERO..Duration::millis(1))
        );
        assert_eq!(
            Duration::ZERO,
            rng.random_range(Duration::ZERO..=Duration::ZERO)
        );

        let low = Duration::millis(100);
        let high = Duration::millis(110);
        for _ in 0..1000 {
            let x = rng.random_range(low..high);
            assert!((low..high).contains(&x));
        }
    }
}
