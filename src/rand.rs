use rand::distributions::uniform::SampleBorrow;
use rand::distributions::uniform::SampleUniform;
use rand::distributions::uniform::UniformInt;
use rand::distributions::uniform::UniformSampler;
use rand::distributions::Distribution;
use rand::distributions::Standard;
use rand::Rng;

use crate::Duration;
use crate::Time;

impl Distribution<Time> for Standard {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Time {
        Time(rng.gen())
    }
}

#[derive(Debug, Clone, Copy)]
pub struct UniformTime(UniformInt<i64>);

impl UniformSampler for UniformTime {
    type X = Time;

    fn new<B1, B2>(low: B1, high: B2) -> Self
    where
        B1: SampleBorrow<Self::X> + Sized,
        B2: SampleBorrow<Self::X> + Sized,
    {
        Self(UniformInt::new(low.borrow().0, high.borrow().0))
    }

    fn new_inclusive<B1, B2>(low: B1, high: B2) -> Self
    where
        B1: SampleBorrow<Self::X> + Sized,
        B2: SampleBorrow<Self::X> + Sized,
    {
        Self(UniformInt::new_inclusive(low.borrow().0, high.borrow().0))
    }

    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Self::X {
        Time(self.0.sample(rng))
    }
}

impl SampleUniform for Time {
    type Sampler = UniformTime;
}

impl Distribution<Duration> for Standard {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Duration {
        Duration(rng.gen())
    }
}

#[derive(Debug, Clone, Copy)]
pub struct UniformDuration(UniformInt<i64>);

impl UniformSampler for UniformDuration {
    type X = Duration;

    fn new<B1, B2>(low: B1, high: B2) -> Self
    where
        B1: SampleBorrow<Self::X> + Sized,
        B2: SampleBorrow<Self::X> + Sized,
    {
        Self(UniformInt::new(low.borrow().0, high.borrow().0))
    }

    fn new_inclusive<B1, B2>(low: B1, high: B2) -> Self
    where
        B1: SampleBorrow<Self::X> + Sized,
        B2: SampleBorrow<Self::X> + Sized,
    {
        Self(UniformInt::new_inclusive(low.borrow().0, high.borrow().0))
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
        let _: Time = rand::thread_rng().gen();
    }

    #[test]
    fn uniform_time() {
        let mut rng = rand::thread_rng();
        assert_eq!(Time::EPOCH, rng.gen_range(Time::EPOCH..Time::millis(1)));
        assert_eq!(Time::EPOCH, rng.gen_range(Time::EPOCH..=Time::EPOCH));

        let low = Time::millis(100);
        let high = Time::millis(110);
        for _ in 0..1000 {
            let x = rng.gen_range(low..high);
            assert!((low..high).contains(&x));
        }
    }

    #[test]
    fn standard_duration() {
        let _: Duration = rand::random();
        let _: Duration = rand::thread_rng().gen();
    }

    #[test]
    fn uniform_duration() {
        let mut rng = rand::thread_rng();
        assert_eq!(
            Duration::ZERO,
            rng.gen_range(Duration::ZERO..Duration::millis(1))
        );
        assert_eq!(
            Duration::ZERO,
            rng.gen_range(Duration::ZERO..=Duration::ZERO)
        );

        let low = Duration::millis(100);
        let high = Duration::millis(110);
        for _ in 0..1000 {
            let x = rng.gen_range(low..high);
            assert!((low..high).contains(&x));
        }
    }
}
