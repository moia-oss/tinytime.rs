//! Low overhead implementation of time related concepts.
//!
//!  # Operator support
//!
//! ```no_run
//! # use tinytime::Duration;
//! # use tinytime::Time;
//! # use tinytime::TimeWindow;
//! # let mut time = Time::hours(3);
//! # let mut duration = Duration::minutes(4);
//! # let mut time_window = TimeWindow::new(Time::hours(2), Time::hours(3));
//! // | example                                       | left       | op | right    | result     |
//! // | ----------------------------------------------| ---------- | ---| -------- | ---------- |
//! let result: Duration = time - time;             // | Time       | -  | Time     | Duration   |
//! let result: Time = time + duration;             // | Time       | +  | Duration | Time       |
//! time += duration;                               // | Time       | += | Duration | Time       |
//! let result: Time = time - duration;             // | Time       | -  | Duration | Time       |
//! time -= duration;                               // | Time       | -= | Duration | Time       |
//! let result: Duration = duration + duration;     // | Duration   | +  | Duration | Duration   |
//! duration += duration;                           // | Duration   | += | Duration | Duration   |
//! let result: Duration = duration - duration;     // | Duration   | -  | Duration | Duration   |
//! duration -= duration;                           // | Duration   | -= | Duration | Duration   |
//! let result: Duration = duration * 1.0f64;       // | Duration   | *  | f64      | Duration   |
//! let result: Duration = 2.0f64 * duration;       // | f64        | *  | Duration | Duration   |
//! duration *= 2.0f64;                             // | Duration   | *= | f64      | Duration   |
//! let result: Duration = duration / 2.0f64;       // | Duration   | /  | f64      | Duration   |
//! duration /= 2.0f64;                             // | Duration   | /= | f64      | Duration   |
//! let result: Duration = duration * 7i64;         // | Duration   | *  | i64      | Duration   |
//! let result: Duration = 7i64 * duration;         // | i64        | *  | Duration | Duration   |
//! duration *= 7i64;                               // | Duration   | *= | i64      | Duration   |
//! let result: Duration = duration / 7i64;         // | Duration   | /  | i64      | Duration   |
//! duration /= 7i64;                               // | Duration   | /= | i64      | Duration   |
//! let result: f64 = duration / duration;          // | Duration   | /  | Duration | f64        |

//! ```

#[cfg(feature = "chrono")]
pub mod chrono;
#[cfg(feature = "rand")]
pub mod rand;
#[cfg(feature = "serde")]
pub mod serde;

use core::fmt;
use std::cmp::Ordering;
use std::cmp::max;
use std::cmp::min;
use std::error::Error;
use std::fmt::Debug;
use std::fmt::Display;
use std::fmt::Formatter;
use std::iter::Sum;
use std::ops::Add;
use std::ops::AddAssign;
use std::ops::Deref;
use std::ops::Div;
use std::ops::DivAssign;
use std::ops::Mul;
use std::ops::MulAssign;
use std::ops::Neg;
use std::ops::Rem;
use std::ops::RemAssign;
use std::ops::Sub;
use std::ops::SubAssign;
use std::str::FromStr;
use std::time::SystemTime;

/// A point in time.
///
/// Low overhead time representation. Internally represented as milliseconds.
#[derive(Eq, PartialEq, Hash, Ord, PartialOrd, Copy, Clone, Default)]
#[cfg_attr(feature = "serde", derive(::serde::Serialize, ::serde::Deserialize))]
#[cfg_attr(feature = "bincode", derive(::bincode::Encode, ::bincode::Decode))]
pub struct Time(i64);

impl Time {
    pub const MAX: Self = Self(i64::MAX);
    pub const EPOCH: Self = Self(0);

    const SECOND: Time = Time(1000);
    const MINUTE: Time = Time(60 * Self::SECOND.0);
    const HOUR: Time = Time(60 * Self::MINUTE.0);

    #[must_use]
    pub const fn millis(millis: i64) -> Self {
        Time(millis)
    }

    #[must_use]
    pub const fn seconds(seconds: i64) -> Self {
        Time::millis(seconds * Self::SECOND.0)
    }

    #[must_use]
    pub const fn minutes(minutes: i64) -> Self {
        Time::millis(minutes * Self::MINUTE.0)
    }

    #[must_use]
    pub const fn hours(hours: i64) -> Self {
        Time::millis(hours * Self::HOUR.0)
    }

    /// Returns the current time instance based on `SystemTime`
    ///
    /// Don't use this method to compare if the current time has passed a
    /// certain deadline.
    #[must_use]
    pub fn now() -> Time {
        Time::from(SystemTime::now())
    }

    /// Returns the number of whole seconds in the time.
    ///
    /// # Examples
    ///
    /// ```
    /// # use tinytime::Time;
    /// assert_eq!(Time::minutes(1).as_seconds(), 60);
    /// ```
    #[must_use]
    pub const fn as_seconds(&self) -> i64 {
        self.0 / Self::SECOND.0
    }

    #[must_use]
    pub const fn as_millis(&self) -> i64 {
        self.0
    }

    /// Returns the number of subsecond millis converted to nanos.
    ///
    /// # Examples
    ///
    /// ```
    /// # use tinytime::Time;
    /// assert_eq!(Time::millis(12345).as_subsecond_nanos(), 345_000_000);
    /// ```
    #[must_use]
    pub const fn as_subsecond_nanos(&self) -> i32 {
        (self.0 % Self::SECOND.0 * 1_000_000) as i32
    }

    /// Rounds time down to a step size
    ///
    /// # Examples
    ///
    /// ```
    /// # use tinytime::Duration;
    /// # use tinytime::Time;
    /// assert_eq!(
    ///     Time::minutes(7).round_down(Duration::minutes(5)),
    ///     Time::minutes(5)
    /// );
    /// assert_eq!(
    ///     Time::minutes(5).round_down(Duration::minutes(5)),
    ///     Time::minutes(5)
    /// );
    /// ```
    #[must_use]
    pub const fn round_down(&self, step_size: Duration) -> Time {
        let time_milli = self.as_millis();
        let part = time_milli % step_size.as_millis().abs();
        Time::millis(time_milli - part)
    }

    /// Rounds time up to a step size
    ///
    /// # Examples
    ///
    /// ```
    /// # use tinytime::Duration;
    /// # use tinytime::Time;
    /// assert_eq!(
    ///     Time::minutes(7).round_up(Duration::minutes(5)),
    ///     Time::minutes(10)
    /// );
    /// assert_eq!(
    ///     Time::minutes(5).round_up(Duration::minutes(5)),
    ///     Time::minutes(5)
    /// );
    /// ```
    #[must_use]
    pub const fn round_up(&self, step_size: Duration) -> Time {
        let time_milli = self.as_millis();
        let step_milli = step_size.as_millis().abs();
        let part = time_milli % step_milli;
        let remaining = (step_milli - part) % step_milli;
        Time::millis(time_milli + remaining)
    }

    /// Checked time duration substraction. Computes `self - rhs`, returning
    /// `None` if overflow occurred.
    ///
    /// # Examples
    /// ```
    /// # use tinytime::Duration;
    /// # use tinytime::Time;
    /// assert_eq!(
    ///     Time::minutes(8).checked_sub(Duration::minutes(5)),
    ///     Some(Time::minutes(3))
    /// );
    /// assert_eq!(Time::minutes(3).checked_sub(Duration::minutes(5)), None);
    /// assert_eq!(
    ///     Time::minutes(2).checked_sub(Duration::minutes(2)),
    ///     Some(Time::EPOCH)
    /// );
    /// ```
    #[must_use]
    pub fn checked_sub(&self, rhs: Duration) -> Option<Self> {
        // check for overflow
        if Time::EPOCH + rhs > *self {
            None
        } else {
            Some(*self - rhs)
        }
    }

    #[must_use]
    pub const fn since_epoch(&self) -> Duration {
        Duration::millis(self.as_millis())
    }
}

impl Deref for Time {
    type Target = i64;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl From<Time> for i64 {
    fn from(time: Time) -> Self {
        time.0
    }
}

impl From<i64> for Time {
    fn from(value: i64) -> Self {
        Self(value)
    }
}

impl TryFrom<Duration> for Time {
    type Error = &'static str;
    fn try_from(duration: Duration) -> Result<Self, Self::Error> {
        if duration.is_non_negative() {
            Ok(Time::millis(duration.as_millis()))
        } else {
            Err("Duration cannot be negative.")
        }
    }
}

#[derive(Debug, Copy, Clone)]
pub struct TimeIsNegativeError;

impl TryFrom<Time> for SystemTime {
    type Error = TimeIsNegativeError;

    fn try_from(input: Time) -> Result<Self, Self::Error> {
        u64::try_from(input.0).map_or(Err(TimeIsNegativeError), |t| {
            Ok(std::time::UNIX_EPOCH + std::time::Duration::from_millis(t))
        })
    }
}

impl From<SystemTime> for Time {
    fn from(input: SystemTime) -> Self {
        let duration = match input.duration_since(SystemTime::UNIX_EPOCH) {
            Ok(std_dur) => Duration::from(std_dur),
            Err(err) => -Duration::from(err.duration()),
        };
        Self::millis(duration.as_millis())
    }
}

impl Debug for Time {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        // This implementation is tailor-made, because NaiveDateTime does not support
        // the full range of Time. For some Time instances it wouldn't be
        // possible to reconstruct them based on the Debug-representation ('∞').
        let positive = self.0 >= 0;
        let mut total = self.0.unsigned_abs();
        let millis_part = total % 1000;
        total -= millis_part;
        let seconds_part = (total % (1000 * 60)) / 1000;
        total -= seconds_part;
        let minutes_part = (total % (1000 * 60 * 60)) / (1000 * 60);
        total -= minutes_part;
        let hours_part = total / (1000 * 60 * 60);
        if !positive {
            f.write_str("-")?;
        }
        write!(f, "{hours_part:02}:")?;
        write!(f, "{minutes_part:02}:")?;
        write!(f, "{seconds_part:02}")?;
        if millis_part > 0 {
            write!(f, ".{millis_part:03}")?;
        }
        Ok(())
    }
}

#[derive(Debug, Eq, PartialEq, Clone, Copy)]
pub enum TimeWindowError {
    StartAfterEnd,
}

impl Display for TimeWindowError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let message = match self {
            Self::StartAfterEnd => "time window start is after end",
        };
        write!(f, "{message}")
    }
}

impl Error for TimeWindowError {}

/// An interval or range of time: `[start,end)`.
/// Debug-asserts ensure that start <= end.
/// If compiled in release mode, the invariant of start <= end is maintained, by
/// correcting invalid use of the API (and setting end to start).
#[derive(Clone, Debug, Eq, PartialEq, Default, Copy, Hash)]
#[cfg_attr(feature = "serde", derive(::serde::Serialize, ::serde::Deserialize))]
#[cfg_attr(feature = "bincode", derive(::bincode::Encode, ::bincode::Decode))]
pub struct TimeWindow {
    start: Time,
    end: Time,
}

impl TimeWindow {
    /// Constructs a new [`TimeWindow`].
    /// `debug_asserts` that `start < end`. Sets end to `start` in release mode
    /// if `start > end`.
    #[must_use]
    pub fn new(start: Time, end: Time) -> Self {
        debug_assert!(start <= end);
        TimeWindow {
            start,
            end: end.max(start),
        }
    }

    /// Constructs a new [`TimeWindow`]. Validates that `start <= end` and
    /// returns an error if not.
    ///
    /// # Examples
    /// ```
    /// # use tinytime::*;
    /// assert!(TimeWindow::new_checked(Time::hours(1), Time::hours(2)).is_ok());
    /// assert_eq!(
    ///     Err(TimeWindowError::StartAfterEnd),
    ///     TimeWindow::new_checked(Time::hours(2), Time::hours(1))
    /// );
    /// ```
    pub fn new_checked(start: Time, end: Time) -> Result<Self, TimeWindowError> {
        if start <= end {
            Ok(TimeWindow { start, end })
        } else {
            Err(TimeWindowError::StartAfterEnd)
        }
    }

    /// Returns [`TimeWindow`] with range [[`Time::EPOCH`], `end`)
    #[must_use]
    pub fn epoch_to(end: Time) -> Self {
        Self::new(Time::EPOCH, end)
    }

    #[must_use]
    pub fn from_minutes(a: i64, b: i64) -> Self {
        TimeWindow::new(Time::minutes(a), Time::minutes(b))
    }

    #[must_use]
    pub fn from_seconds(a: i64, b: i64) -> Self {
        TimeWindow::new(Time::seconds(a), Time::seconds(b))
    }

    /// Creates time window from start time and length.
    ///
    /// Negative lengths are treated as [`Duration::ZERO`].
    ///
    /// # Examples
    /// ```
    /// # use tinytime::*;
    /// assert_eq!(
    ///     TimeWindow::from_seconds(1, 3),
    ///     TimeWindow::from_length_starting_at(Duration::seconds(2), Time::seconds(1))
    /// );
    /// assert_eq!(
    ///     TimeWindow::from_seconds(1, 1),
    ///     TimeWindow::from_length_starting_at(Duration::seconds(-2), Time::seconds(1))
    /// );
    /// ```
    #[must_use]
    pub fn from_length_starting_at(length: Duration, start: Time) -> Self {
        TimeWindow::new(start, start.add(length.max(Duration::ZERO)))
    }

    /// Creates time window from length and end time.
    ///
    /// Negative lengths are treated as [`Duration::ZERO`].
    ///
    ///  # Examples
    /// ```
    /// # use tinytime::*;
    /// assert_eq!(
    ///     TimeWindow::from_seconds(1, 3),
    ///     TimeWindow::from_length_ending_at(Duration::seconds(2), Time::seconds(3))
    /// );
    /// assert_eq!(
    ///     TimeWindow::from_seconds(3, 3),
    ///     TimeWindow::from_length_ending_at(Duration::seconds(-2), Time::seconds(3))
    /// );
    /// ```
    #[must_use]
    pub fn from_length_ending_at(length: Duration, end: Time) -> Self {
        TimeWindow::new(end.sub(length.max(Duration::ZERO)), end)
    }

    #[must_use]
    pub const fn instant(time: Time) -> Self {
        TimeWindow {
            start: time,
            end: time,
        }
    }

    #[must_use]
    pub const fn widest() -> Self {
        TimeWindow {
            start: Time::EPOCH,
            end: Time::MAX,
        }
    }

    #[must_use]
    pub fn instant_seconds(seconds: i64) -> Self {
        TimeWindow::from_seconds(seconds, seconds)
    }

    #[must_use]
    pub const fn start(&self) -> Time {
        self.start
    }

    #[must_use]
    pub const fn end(&self) -> Time {
        self.end
    }

    #[must_use]
    pub fn length(&self) -> Duration {
        self.end - self.start
    }

    /// Creates a new `TimeWindow` with `start` set to `new_start`. If
    /// `new_start` is greater than or equal to `end` the start will be set
    /// equal to `end`.
    #[must_use]
    pub fn with_start(&self, new_start: Time) -> Self {
        Self::new(new_start.min(self.end), self.end)
    }

    /// Creates a new `TimeWindow` with `end` set to `new_end`. If `new_end` is
    /// smaller or equal to `start`, the `end` will be set to `start.`
    #[must_use]
    pub fn with_end(&self, new_end: Time) -> Self {
        Self::new(self.start, new_end.max(self.start))
    }

    /// Creates a new `TimeWindow` with the `start` preponed to the given value.
    /// If `new_start` isn't earlier than the current time window start, a copy
    /// of `self` is returned.
    ///
    /// # Examples
    /// ```
    /// # use tinytime::*;
    /// let x = TimeWindow::from_seconds(4, 5);
    /// assert_eq!(
    ///     TimeWindow::from_seconds(3, 5),
    ///     x.prepone_start_to(Time::seconds(3))
    /// );
    /// assert_eq!(
    ///     TimeWindow::from_seconds(4, 5),
    ///     x.prepone_start_to(Time::seconds(6))
    /// );
    /// ```
    #[must_use]
    pub fn prepone_start_to(&self, new_start: Time) -> Self {
        self.with_start(self.start.min(new_start))
    }

    /// Creates a new `TimeWindow` with the `start` preponed by the given
    /// duration.
    ///
    /// Negative durations are treated as [`Duration::ZERO`].
    ///
    /// # Examples
    /// ```
    /// # use tinytime::*;
    /// let tw = TimeWindow::from_seconds(8, 9);
    /// assert_eq!(
    ///     TimeWindow::from_seconds(5, 9),
    ///     tw.prepone_start_by(Duration::seconds(3))
    /// );
    /// assert_eq!(
    ///     TimeWindow::from_seconds(8, 9),
    ///     tw.prepone_start_by(Duration::seconds(-3))
    /// );
    /// ```
    #[must_use]
    pub fn prepone_start_by(&self, duration: Duration) -> Self {
        self.with_start(self.start - duration.max(Duration::ZERO))
    }

    /// Creates a new `TimeWindow` with the `start` preponed so that the new
    /// time window length matches the given value.
    ///
    /// Returns a copy of `self` if the new length is smaller than
    /// [`Self::length()`].
    ///
    /// # Examples
    /// ```
    /// # use tinytime::*;
    /// let tw = TimeWindow::from_seconds(1, 3);
    /// assert_eq!(
    ///     TimeWindow::from_seconds(1, 3),
    ///     tw.prepone_start_extend_to(Duration::seconds(-1))
    /// );
    /// assert_eq!(
    ///     TimeWindow::from_seconds(1, 3),
    ///     tw.prepone_start_extend_to(Duration::seconds(0))
    /// );
    /// assert_eq!(
    ///     TimeWindow::from_seconds(-2, 3),
    ///     tw.prepone_start_extend_to(Duration::seconds(5))
    /// );
    /// ```
    #[must_use]
    pub fn prepone_start_extend_to(&self, new_length: Duration) -> Self {
        self.with_start(self.end - new_length.max(self.length()))
    }

    /// Creates a new `TimeWindow` with the `start` postponed to the given
    /// value.
    ///
    /// Returns a copy of `self` when the given value isn't later than the
    /// current time window start. Will never postpone the start past the
    /// end of the time window.
    ///
    /// # Examples
    /// ```
    /// # use tinytime::*;
    /// let tw = TimeWindow::from_seconds(1, 3);
    /// assert_eq!(
    ///     TimeWindow::from_seconds(1, 3),
    ///     tw.postpone_start_to(Time::EPOCH)
    /// );
    /// assert_eq!(
    ///     TimeWindow::from_seconds(2, 3),
    ///     tw.postpone_start_to(Time::seconds(2))
    /// );
    /// assert_eq!(
    ///     TimeWindow::from_seconds(3, 3),
    ///     tw.postpone_start_to(Time::seconds(3))
    /// );
    /// ```
    #[must_use]
    pub fn postpone_start_to(&self, new_start: Time) -> Self {
        self.with_start(self.start.max(new_start))
    }

    /// Creates a new `TimeWindow` with the `start` postponed by the given
    /// duration.
    ///
    /// Negative durations are treated as [`Duration::ZERO`]. Will not postpone
    /// `start` further than `end`.
    ///
    /// # Examples
    /// ```
    /// # use tinytime::*;
    /// let tw = TimeWindow::from_seconds(1, 5);
    /// assert_eq!(
    ///     TimeWindow::from_seconds(4, 5),
    ///     tw.postpone_start_by(Duration::seconds(3))
    /// );
    /// assert_eq!(
    ///     TimeWindow::from_seconds(5, 5),
    ///     tw.postpone_start_by(Duration::seconds(30))
    /// );
    /// assert_eq!(
    ///     TimeWindow::from_seconds(1, 5),
    ///     tw.postpone_start_by(Duration::seconds(-3))
    /// );
    /// ```
    #[must_use]
    pub fn postpone_start_by(&self, duration: Duration) -> Self {
        self.with_start(self.start + duration.max(Duration::ZERO))
    }

    /// Creates a new `TimeWindow` with the `start` postponed so that the new
    /// time window length matches the given value.
    ///
    /// Returns a copy of `self` if the new length is smaller than the current
    /// one. Negative length will set the resulting time window length to zero.
    ///
    /// # Examples
    /// ```
    /// # use tinytime::*;
    /// let tw = TimeWindow::from_seconds(1, 3);
    /// assert_eq!(
    ///     TimeWindow::from_seconds(3, 3),
    ///     tw.postpone_start_shrink_to(Duration::seconds(-1))
    /// );
    /// assert_eq!(
    ///     TimeWindow::from_seconds(3, 3),
    ///     tw.postpone_start_shrink_to(Duration::seconds(0))
    /// );
    /// assert_eq!(
    ///     TimeWindow::from_seconds(2, 3),
    ///     tw.postpone_start_shrink_to(Duration::seconds(1))
    /// );
    /// assert_eq!(
    ///     TimeWindow::from_seconds(1, 3),
    ///     tw.postpone_start_shrink_to(Duration::seconds(5))
    /// );
    /// ```
    #[must_use]
    pub fn postpone_start_shrink_to(&self, new_length: Duration) -> Self {
        let length = new_length
            .min(self.length()) // Resize only if new length is smaller than the current one
            .max(Duration::ZERO); // Make sure the new length is non-negative
        self.with_start(self.end - length)
    }

    /// Creates a new `TimeWindow` with the `end` preponed to the given value.
    ///
    /// Returns a copy of `self` when the given value isn't earlier than the
    /// current time window end. Will never prepone the end more than to the
    /// start of the time window.
    ///
    /// # Examples
    /// ```
    /// # use tinytime::*;
    /// let tw = TimeWindow::from_seconds(1, 3);
    /// assert_eq!(
    ///     TimeWindow::from_seconds(1, 3),
    ///     tw.prepone_end_to(Time::seconds(4))
    /// );
    /// assert_eq!(
    ///     TimeWindow::from_seconds(1, 2),
    ///     tw.prepone_end_to(Time::seconds(2))
    /// );
    /// assert_eq!(
    ///     TimeWindow::from_seconds(1, 1),
    ///     tw.prepone_end_to(Time::EPOCH)
    /// );
    /// ```
    #[must_use]
    pub fn prepone_end_to(&self, new_end: Time) -> Self {
        self.with_end(self.end.min(new_end))
    }

    /// Creates a new `TimeWindow` with the `end` preponed by the given
    /// duration.
    ///
    /// Negative durations are treated as [`Duration::ZERO`]. Will not prepone
    /// `end` before `end`.
    ///
    /// # Examples
    /// ```
    /// # use tinytime::*;
    /// let tw = TimeWindow::from_seconds(4, 9);
    /// assert_eq!(
    ///     TimeWindow::from_seconds(4, 6),
    ///     tw.prepone_end_by(Duration::seconds(3))
    /// );
    /// assert_eq!(
    ///     TimeWindow::from_seconds(4, 4),
    ///     tw.prepone_end_by(Duration::seconds(30))
    /// );
    /// assert_eq!(
    ///     TimeWindow::from_seconds(4, 9),
    ///     tw.prepone_end_by(Duration::seconds(-3))
    /// );
    /// ```
    #[must_use]
    pub fn prepone_end_by(&self, duration: Duration) -> Self {
        self.with_end(self.end - duration.max(Duration::ZERO))
    }

    /// Creates a new `TimeWindow` with the `end` preponed so that the new time
    /// window length matches the given value.
    ///
    /// Returns a copy of `self` if the new length is smaller than the current
    /// one. Negative length will set the resulting time window length to zero.
    ///
    /// # Examples
    /// ```
    /// # use tinytime::*;
    /// let tw = TimeWindow::from_seconds(1, 3);
    /// assert_eq!(
    ///     TimeWindow::from_seconds(1, 1),
    ///     tw.prepone_end_shrink_to(Duration::seconds(-1))
    /// );
    /// assert_eq!(
    ///     TimeWindow::from_seconds(1, 1),
    ///     tw.prepone_end_shrink_to(Duration::seconds(0))
    /// );
    /// assert_eq!(
    ///     TimeWindow::from_seconds(1, 2),
    ///     tw.prepone_end_shrink_to(Duration::seconds(1))
    /// );
    /// assert_eq!(
    ///     TimeWindow::from_seconds(1, 3),
    ///     tw.prepone_end_shrink_to(Duration::seconds(5))
    /// );
    /// ```
    #[must_use]
    pub fn prepone_end_shrink_to(&self, new_length: Duration) -> Self {
        let length = new_length
            .min(self.length()) // Resize only if new length is smaller than the current one
            .max(Duration::ZERO); // Make sure the new length is non-negative
        self.with_end(self.start + length)
    }

    /// Creates a new `TimeWindow` with the `end` postponed to the given value.
    /// If `new_end` isn't later than the current time window end, a copy of
    /// `self` is returned.
    ///
    /// # Examples
    /// ```
    /// # use tinytime::*;
    /// let x = TimeWindow::from_seconds(1, 2);
    /// assert_eq!(
    ///     TimeWindow::from_seconds(1, 3),
    ///     x.postpone_end_to(Time::seconds(3))
    /// );
    /// assert_eq!(
    ///     TimeWindow::from_seconds(1, 2),
    ///     x.postpone_end_to(Time::EPOCH)
    /// );
    /// ```
    #[must_use]
    pub fn postpone_end_to(&self, new_end: Time) -> Self {
        self.with_end(self.end.max(new_end))
    }

    /// Creates a new `TimeWindow` with the `end` postponed by the given
    /// duration.
    ///
    /// Negative durations are treated as [`Duration::ZERO`].
    ///
    /// # Examples
    /// ```
    /// # use tinytime::*;
    /// let tw = TimeWindow::from_seconds(1, 2);
    /// assert_eq!(
    ///     TimeWindow::from_seconds(1, 5),
    ///     tw.postpone_end_by(Duration::seconds(3))
    /// );
    /// assert_eq!(
    ///     TimeWindow::from_seconds(1, 2),
    ///     tw.postpone_end_by(Duration::seconds(-3))
    /// );
    /// ```
    #[must_use]
    pub fn postpone_end_by(&self, duration: Duration) -> Self {
        self.with_end(self.end + duration.max(Duration::ZERO))
    }

    /// Creates a new `TimeWindow` with the `end` postponed so that the new
    /// time window length matches the given value.
    ///
    /// Returns a copy of `self` if the new length is smaller than
    /// [`Self::length()`].
    ///
    /// # Examples
    /// ```
    /// # use tinytime::*;
    /// let tw = TimeWindow::from_seconds(1, 3);
    /// assert_eq!(
    ///     TimeWindow::from_seconds(1, 3),
    ///     tw.postpone_end_extend_to(Duration::seconds(-1))
    /// );
    /// assert_eq!(
    ///     TimeWindow::from_seconds(1, 3),
    ///     tw.postpone_end_extend_to(Duration::seconds(0))
    /// );
    /// assert_eq!(
    ///     TimeWindow::from_seconds(1, 6),
    ///     tw.postpone_end_extend_to(Duration::seconds(5))
    /// );
    /// ```
    #[must_use]
    pub fn postpone_end_extend_to(&self, new_length: Duration) -> Self {
        self.with_end(self.start + new_length.max(self.length()))
    }

    /// Returns true if this time window contains the given time.
    /// # Examples
    ///
    /// ```
    /// # use tinytime::{Time, TimeWindow};
    /// let mut x = TimeWindow::from_seconds(5, 10);
    /// assert!(!x.contains(Time::seconds(4)));
    /// assert!(x.contains(Time::seconds(5)));
    /// assert!(x.contains(Time::seconds(7)));
    /// assert!(x.contains(Time::seconds(10)));
    /// assert!(!x.contains(Time::seconds(11)));
    /// ```
    #[must_use]
    pub fn contains(&self, that: Time) -> bool {
        self.start <= that && that <= self.end
    }

    /// Returns true if this time window overlaps with another one
    /// # Examples
    ///
    /// ```
    /// # use tinytime::TimeWindow;
    /// let mut x = TimeWindow::from_seconds(5, 10);
    /// assert!(x.overlaps(&TimeWindow::from_seconds(5, 10)));
    /// assert!(x.overlaps(&TimeWindow::from_seconds(3, 12)));
    /// assert!(x.overlaps(&TimeWindow::from_seconds(6, 9)));
    /// assert!(x.overlaps(&TimeWindow::from_seconds(6, 12)));
    /// assert!(x.overlaps(&TimeWindow::from_seconds(3, 9)));
    /// assert!(!x.overlaps(&TimeWindow::from_seconds(1, 4)));
    /// assert!(!x.overlaps(&TimeWindow::from_seconds(1, 5)));
    /// assert!(!x.overlaps(&TimeWindow::from_seconds(10, 15)));
    /// assert!(!x.overlaps(&TimeWindow::from_seconds(11, 15)));
    /// ```
    #[must_use]
    pub fn overlaps(&self, that: &TimeWindow) -> bool {
        self.start < that.end && that.start < self.end
    }

    /// Returns time window that is an intersection between this time window and
    /// another one. Returns None if time windows don't overlap.
    /// # Examples
    ///
    /// ```
    /// # use tinytime::TimeWindow;
    /// let x = TimeWindow::from_seconds(5, 10);
    /// assert_eq!(
    ///     Some(TimeWindow::from_seconds(5, 10)),
    ///     x.intersect(&TimeWindow::from_seconds(5, 10)),
    ///     "time windows are equal"
    /// );
    /// assert_eq!(
    ///     Some(TimeWindow::from_seconds(5, 10)),
    ///     x.intersect(&TimeWindow::from_seconds(3, 12)),
    ///     "that contains x"
    /// );
    /// assert_eq!(
    ///     Some(TimeWindow::from_seconds(6, 9)),
    ///     x.intersect(&TimeWindow::from_seconds(6, 9)),
    ///     "x contains that"
    /// );
    /// assert_eq!(
    ///     Some(TimeWindow::from_seconds(6, 10)),
    ///     x.intersect(&TimeWindow::from_seconds(6, 12))
    /// );
    /// assert_eq!(
    ///     Some(TimeWindow::from_seconds(5, 9)),
    ///     x.intersect(&TimeWindow::from_seconds(3, 9))
    /// );
    /// assert_eq!(
    ///     None,
    ///     x.intersect(&TimeWindow::from_seconds(1, 4)),
    ///     "that is before x"
    /// );
    /// assert_eq!(
    ///     Some(TimeWindow::from_seconds(5, 5)),
    ///     x.intersect(&TimeWindow::from_seconds(1, 5)),
    ///     "single-point intersection"
    /// );
    /// assert_eq!(
    ///     Some(TimeWindow::from_seconds(10, 10)),
    ///     x.intersect(&TimeWindow::from_seconds(10, 15)),
    ///     "single-point intersection"
    /// );
    /// assert_eq!(
    ///     None,
    ///     x.intersect(&TimeWindow::from_seconds(11, 15)),
    ///     "that is after x"
    /// );
    /// ```
    #[must_use]
    pub fn intersect(&self, that: &TimeWindow) -> Option<TimeWindow> {
        let start = max(self.start, that.start);
        let end = min(self.end, that.end);
        (start <= end).then(|| TimeWindow::new(start, end))
    }

    /// Shifts this time window by `duration` into the future. Affects both
    /// `start` and `end` equally, leaving the length untouched.
    ///
    /// # Examples
    ///
    /// ```
    /// # use tinytime::TimeWindow;
    /// # use tinytime::Duration;
    /// # use tinytime::Time;
    /// let mut tw = TimeWindow::new(Time::EPOCH, Time::minutes(15));
    /// // shift to the future
    /// tw.shift(Duration::minutes(30));
    /// assert_eq!(TimeWindow::new(Time::minutes(30), Time::minutes(45)), tw);
    /// // shift into the past
    /// tw.shift(-Duration::minutes(15));
    /// assert_eq!(TimeWindow::new(Time::minutes(15), Time::minutes(30)), tw);
    /// ```
    pub fn shift(&mut self, duration: Duration) {
        self.start += duration;
        self.end += duration;
    }
}

impl From<TimeWindow> for (Time, Time) {
    fn from(tw: TimeWindow) -> Self {
        (tw.start, tw.end)
    }
}

impl From<(Time, Time)> for TimeWindow {
    fn from((start, end): (Time, Time)) -> Self {
        Self { start, end }
    }
}

/// A duration of time.
///
/// Duration can be negative. Internally duration is represented as
/// milliseconds.
#[derive(Eq, PartialEq, Ord, PartialOrd, Copy, Clone, Default, Hash)]
#[cfg_attr(feature = "serde", derive(::serde::Serialize, ::serde::Deserialize))]
#[cfg_attr(feature = "bincode", derive(::bincode::Encode, ::bincode::Decode))]
pub struct Duration(i64);

impl Duration {
    pub const ZERO: Self = Self(0_i64);
    pub const MAX: Self = Self(i64::MAX);

    const SECOND: Duration = Duration(1000);
    const MINUTE: Duration = Duration(60 * Self::SECOND.0);
    const HOUR: Duration = Duration(60 * Self::MINUTE.0);

    /// Create a duration instance from hours
    #[must_use]
    pub const fn hours(hours: i64) -> Self {
        Duration(hours * Self::HOUR.0)
    }

    /// Create a duration instance from minutes.
    #[must_use]
    pub const fn minutes(minutes: i64) -> Self {
        Duration(minutes * Self::MINUTE.0)
    }

    /// Create a duration instance from seconds.
    #[must_use]
    pub const fn seconds(seconds: i64) -> Self {
        Duration(seconds * Self::SECOND.0)
    }

    /// Create a duration instance from ms.
    #[must_use]
    pub const fn millis(ms: i64) -> Self {
        Duration(ms)
    }

    #[must_use]
    pub fn abs(&self) -> Self {
        if self >= &Duration::ZERO {
            *self
        } else {
            -*self
        }
    }
    /// Returns the number of whole milliseconds in the Duration instance.
    #[must_use]
    pub const fn as_millis(&self) -> i64 {
        self.0
    }

    /// Returns the number of non-negative whole milliseconds in the Duration
    /// instance.
    #[must_use]
    pub const fn as_millis_unsigned(&self) -> u64 {
        as_unsigned(self.0)
    }

    /// Returns the number of whole seconds in the Duration instance.
    #[must_use]
    pub const fn as_seconds(&self) -> i64 {
        self.0 / Self::SECOND.0
    }

    /// Returns the number of non-negative whole seconds in the Duration
    /// instance.
    #[must_use]
    pub const fn as_seconds_unsigned(&self) -> u64 {
        as_unsigned(self.0 / 1000)
    }

    /// Returns the number of whole minutes in the Duration instance.
    #[must_use]
    pub const fn as_minutes(&self) -> i64 {
        self.0 / Self::MINUTE.0
    }

    /// Returns true if duration is `>= 0`.
    #[must_use]
    pub const fn is_non_negative(&self) -> bool {
        self.0 >= 0
    }

    /// Returns true if duration is `> 0`.
    #[must_use]
    pub const fn is_positive(&self) -> bool {
        self.0 > 0
    }
}

impl Deref for Duration {
    type Target = i64;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl From<Duration> for i64 {
    fn from(time: Duration) -> Self {
        time.0
    }
}

impl From<i64> for Duration {
    fn from(value: i64) -> Self {
        Self(value)
    }
}

impl Neg for Duration {
    type Output = Self;

    fn neg(self) -> Self::Output {
        Self(-self.0)
    }
}

impl Sum for Duration {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Self::ZERO, Add::add)
    }
}

impl PartialEq<std::time::Duration> for Duration {
    fn eq(&self, other: &std::time::Duration) -> bool {
        (u128::from(self.as_millis_unsigned())).eq(&other.as_millis())
    }
}

impl PartialOrd<std::time::Duration> for Duration {
    fn partial_cmp(&self, other: &std::time::Duration) -> Option<Ordering> {
        (u128::from(self.as_millis_unsigned())).partial_cmp(&other.as_millis())
    }
}

impl Display for Duration {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        if self.0 == 0 {
            return write!(f, "0ms");
        }
        let mut string = String::new();
        if self.0 < 0 {
            string.push('-');
        }
        let abs = self.0.abs();
        let ms = abs % 1000;
        let s = (abs / 1000) % 60;
        let m = (abs / 60000) % 60;
        let h = abs / (60 * 60 * 1000);

        if h > 0 {
            string.push_str(&h.to_string());
            string.push('h');
        }
        if m > 0 {
            string.push_str(&m.to_string());
            string.push('m');
        }
        if s > 0 {
            string.push_str(&s.to_string());
            string.push('s');
        }
        if ms > 0 {
            string.push_str(&ms.to_string());
            string.push_str("ms");
        }

        write!(f, "{string}")
    }
}

impl Debug for Duration {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl From<f64> for Duration {
    fn from(num: f64) -> Self {
        #[expect(clippy::cast_possible_truncation, reason = "expected behavior")]
        {
            Duration::millis(num.round() as i64)
        }
    }
}

impl From<Duration> for f64 {
    fn from(num: Duration) -> Self {
        num.0 as f64
    }
}

/////////////////////////////
// OPERATORS FOR TIME      //
/////////////////////////////

impl Sub<Time> for Time {
    type Output = Duration;

    fn sub(self, rhs: Time) -> Self::Output {
        debug_assert!(
            self.0.checked_sub(rhs.0).is_some(),
            "overflow detected: {self:?} - {rhs:?}"
        );
        Duration(self.0 - rhs.0)
    }
}

impl Add<Duration> for Time {
    type Output = Time;

    fn add(self, rhs: Duration) -> Self::Output {
        debug_assert!(
            self.0.checked_add(rhs.0).is_some(),
            "overflow detected: {self:?} + {rhs:?}"
        );
        Time(self.0 + rhs.0)
    }
}

impl AddAssign<Duration> for Time {
    fn add_assign(&mut self, rhs: Duration) {
        debug_assert!(
            self.0.checked_add(rhs.0).is_some(),
            "overflow detected: {self:?} += {rhs:?}"
        );
        self.0 += rhs.0;
    }
}

impl Sub<Duration> for Time {
    type Output = Time;

    fn sub(self, rhs: Duration) -> Self::Output {
        debug_assert!(
            self.0.checked_sub(rhs.0).is_some(),
            "overflow detected: {self:?} - {rhs:?}"
        );
        Time(self.0 - rhs.0)
    }
}

impl SubAssign<Duration> for Time {
    fn sub_assign(&mut self, rhs: Duration) {
        debug_assert!(
            self.0.checked_sub(rhs.0).is_some(),
            "overflow detected: {self:?} -= {rhs:?}"
        );
        self.0 -= rhs.0;
    }
}

/////////////////////////////
// OPERATORS FOR DURATION  //
/////////////////////////////

impl Add<Duration> for Duration {
    type Output = Duration;

    fn add(self, rhs: Duration) -> Self::Output {
        debug_assert!(
            self.0.checked_add(rhs.0).is_some(),
            "overflow detected: {self:?} + {rhs:?}"
        );
        Duration(self.0 + rhs.0)
    }
}

impl AddAssign<Duration> for Duration {
    fn add_assign(&mut self, rhs: Duration) {
        debug_assert!(
            self.0.checked_add(rhs.0).is_some(),
            "overflow detected: {self:?} += {rhs:?}"
        );
        self.0 += rhs.0;
    }
}

impl Sub<Duration> for Duration {
    type Output = Duration;

    fn sub(self, rhs: Duration) -> Self::Output {
        debug_assert!(
            self.0.checked_sub(rhs.0).is_some(),
            "overflow detected: {self:?} - {rhs:?}"
        );
        Duration(self.0 - rhs.0)
    }
}

impl SubAssign<Duration> for Duration {
    fn sub_assign(&mut self, rhs: Duration) {
        debug_assert!(
            self.0.checked_sub(rhs.0).is_some(),
            "overflow detected: {self:?} -= {rhs:?}"
        );
        self.0 -= rhs.0;
    }
}

impl Mul<f64> for Duration {
    type Output = Duration;

    fn mul(self, rhs: f64) -> Self::Output {
        #[expect(clippy::cast_possible_truncation, reason = "expected behavior")]
        {
            Duration((self.0 as f64 * rhs).round() as i64)
        }
    }
}

impl Mul<Duration> for f64 {
    type Output = Duration;

    fn mul(self, rhs: Duration) -> Self::Output {
        rhs * self
    }
}

impl MulAssign<f64> for Duration {
    fn mul_assign(&mut self, rhs: f64) {
        #[expect(clippy::cast_possible_truncation, reason = "expected behavior")]
        {
            self.0 = (self.0 as f64 * rhs).round() as i64;
        }
    }
}

// Returns rounded Duration
impl Div<f64> for Duration {
    type Output = Duration;

    fn div(self, rhs: f64) -> Self::Output {
        debug_assert!(
            rhs.abs() > f64::EPSILON,
            "Dividing by zero results in INF. This is probably not what you want."
        );
        #[expect(clippy::cast_possible_truncation, reason = "expected behavior")]
        {
            Duration((self.0 as f64 / rhs).round() as i64)
        }
    }
}

impl DivAssign<f64> for Duration {
    fn div_assign(&mut self, rhs: f64) {
        #[expect(clippy::cast_possible_truncation, reason = "expected behavior")]
        {
            self.0 = (self.0 as f64 / rhs).round() as i64;
        }
    }
}

impl Mul<i64> for Duration {
    type Output = Duration;

    fn mul(self, rhs: i64) -> Self::Output {
        debug_assert!(
            self.0.checked_mul(rhs).is_some(),
            "overflow detected: {self:?} * {rhs:?}"
        );
        Duration(self.0 * rhs)
    }
}

impl Mul<Duration> for i64 {
    type Output = Duration;

    fn mul(self, rhs: Duration) -> Self::Output {
        rhs * self
    }
}

impl MulAssign<i64> for Duration {
    fn mul_assign(&mut self, rhs: i64) {
        debug_assert!(
            self.0.checked_mul(rhs).is_some(),
            "overflow detected: {self:?} *= {rhs:?}"
        );
        self.0 *= rhs;
    }
}

impl Div<i64> for Duration {
    type Output = Duration;

    fn div(self, rhs: i64) -> Self::Output {
        // forward to the float implementation
        self / rhs as f64
    }
}

impl DivAssign<i64> for Duration {
    fn div_assign(&mut self, rhs: i64) {
        // forward to the float implementation
        self.div_assign(rhs as f64);
    }
}

impl Div<Duration> for Duration {
    type Output = f64;

    fn div(self, rhs: Duration) -> Self::Output {
        debug_assert_ne!(
            rhs,
            Duration::ZERO,
            "Dividing by zero results in INF. This is probably not what you want."
        );
        self.0 as f64 / rhs.0 as f64
    }
}

impl Rem<Duration> for Time {
    type Output = Duration;

    fn rem(self, rhs: Duration) -> Self::Output {
        Duration(self.0 % rhs.0)
    }
}

impl Rem<Duration> for Duration {
    type Output = Duration;

    fn rem(self, rhs: Duration) -> Self::Output {
        Duration(self.0 % rhs.0)
    }
}

impl RemAssign<Duration> for Duration {
    fn rem_assign(&mut self, rhs: Duration) {
        self.0 %= rhs.0;
    }
}

impl From<Duration> for std::time::Duration {
    fn from(input: Duration) -> Self {
        debug_assert!(
            input.is_non_negative(),
            "Negative Duration {input} cannot be converted to std::time::Duration"
        );
        #[expect(clippy::cast_sign_loss, reason = "caught by the debug_assert above")]
        let secs = (input.0 / 1000) as u64;
        #[expect(
            clippy::cast_possible_truncation,
            clippy::cast_sign_loss,
            reason = "casting to u32 is safe here because it is guaranteed that the value is in 0..1_000_000_000. The sign loss is caught by the debug_assert above."
        )]
        let nanos = ((input.0 % 1000) * 1_000_000) as u32;
        std::time::Duration::new(secs, nanos)
    }
}

impl From<std::time::Duration> for Duration {
    fn from(input: std::time::Duration) -> Self {
        debug_assert!(
            i64::try_from(input.as_millis()).is_ok(),
            "Input std::time::Duration ({input:?}) is too large to be converted to tinytime::Duration"
        );
        #[expect(clippy::cast_possible_truncation, reason = "expected behavior")]
        Duration::millis(input.as_millis() as i64)
    }
}

/// Parses Duration from str
///
/// # Example
/// ```
/// # use tinytime::Duration;
/// # use std::str::FromStr;
/// assert_eq!(Duration::millis(2), Duration::from_str("2ms").unwrap());
/// assert_eq!(Duration::seconds(3), Duration::from_str("3s").unwrap());
/// assert_eq!(Duration::minutes(4), Duration::from_str("4m").unwrap());
/// assert_eq!(Duration::hours(5), Duration::from_str("5h").unwrap());
///
/// assert_eq!(
///     Duration::hours(5) + Duration::minutes(2),
///     Duration::from_str("5h2m").unwrap()
/// );
/// assert_eq!(
///     Duration::hours(5) + Duration::minutes(2) + Duration::millis(1123),
///     Duration::from_str("5h2m1s123ms").unwrap()
/// );
/// assert_eq!(
///     Duration::seconds(5) - Duration::minutes(2),
///     Duration::from_str("-1m55s").unwrap()
/// );
/// ```
impl FromStr for Duration {
    type Err = DurationParseError;

    #[expect(
        clippy::string_slice,
        reason = "all slice indices come from methods that guarantee correctness"
    )]
    fn from_str(mut s: &str) -> Result<Self, Self::Err> {
        let without_sign = s.strip_prefix('-');
        let negative = without_sign.is_some();
        s = without_sign.unwrap_or(s);

        let mut duration = Self::ZERO;
        while !s.is_empty() {
            let without_number = s.trim_start_matches(|c: char| c.is_ascii_digit());
            let Ok(number) = s[..s.len() - without_number.len()].parse::<i64>() else {
                return Err(DurationParseError::UnrecognizedFormat);
            };
            let without_unit = without_number.trim_start_matches(|c: char| !c.is_ascii_digit());
            let unit = &without_number[..without_number.len() - without_unit.len()];

            duration += match unit {
                "h" => Duration::hours(number),
                "m" => Duration::minutes(number),
                "s" => Duration::seconds(number),
                "ms" => Duration::millis(number),
                _ => return Err(DurationParseError::UnrecognizedFormat),
            };
            s = without_unit;
        }

        if negative {
            duration = -duration;
        }

        Ok(duration)
    }
}

#[derive(Debug, Clone, Copy)]
pub enum DurationParseError {
    UnrecognizedFormat,
}

impl Error for DurationParseError {}

impl Display for DurationParseError {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "Unrecognized Duration format, valid examples are '2h3s', '1m', '1h3m5s700ms'"
        )
    }
}

/// Work-around for `max` in `std` not being const
const fn as_unsigned(x: i64) -> u64 {
    if x >= 0 { x as u64 } else { 0 }
}

#[cfg(test)]
mod time_test {
    use crate::Duration;
    use crate::Time;

    #[test]
    fn test_display() {
        struct TestCase {
            name: &'static str,
            input: Time,
            expected: String,
        }
        let tests = vec![
            TestCase {
                name: "EPOCH",
                input: Time::EPOCH,
                expected: "1970-01-01T00:00:00+00:00".to_string(),
            },
            TestCase {
                name: "i16::MAX + 1",
                input: Time::seconds(i64::from(i16::MAX) + 1),
                expected: "1970-01-01T09:06:08+00:00".to_string(),
            },
            TestCase {
                name: "i32::MAX + 1",
                input: Time::seconds(i64::from(i32::MAX) + 1),
                expected: "2038-01-19T03:14:08+00:00".to_string(),
            },
            TestCase {
                name: "u32::MAX + 1",
                input: Time::seconds(i64::from(u32::MAX) + 1),
                expected: "2106-02-07T06:28:16+00:00".to_string(),
            },
            TestCase {
                name: "very large",
                input: Time::seconds(i64::from(i32::MAX) * 3500),
                expected: "+240148-08-31T19:28:20+00:00".to_string(),
            },
            TestCase {
                name: "MAX",
                input: Time::MAX,
                expected: "∞".to_string(),
            },
            TestCase {
                name: "i16::MIN",
                input: Time::seconds(i64::from(i16::MIN)),
                expected: "1969-12-31T14:53:52+00:00".to_string(),
            },
            TestCase {
                name: "i64::MIN",
                input: Time::millis(i64::MIN),
                expected: "∞".to_string(),
            },
        ];
        for test in tests {
            assert_eq!(
                test.expected,
                test.input.to_rfc3339(),
                "to_rfc3339 failed for test '{}'",
                test.name
            );
            assert_eq!(
                test.expected,
                test.input.format("%Y-%m-%dT%H:%M:%S+00:00").to_string(),
                "format failed for test '{}'",
                test.name
            );
        }
    }

    #[test]
    fn test_debug() {
        struct TestCase {
            name: &'static str,
            input: Time,
            expected: String,
        }
        let tests = vec![
            TestCase {
                name: "EPOCH",
                input: Time::EPOCH,
                expected: "00:00:00".to_string(),
            },
            TestCase {
                name: "i16::MAX + 1",
                input: Time::seconds(i64::from(i16::MAX) + 1),
                expected: "09:06:08".to_string(),
            },
            TestCase {
                name: "i32::MAX + 1",
                input: Time::seconds(i64::from(i32::MAX) + 1),
                expected: "596523:14:08".to_string(),
            },
            TestCase {
                name: "u32::MAX + 1",
                input: Time::seconds(i64::from(u32::MAX) + 1),
                expected: "1193046:28:16".to_string(),
            },
            TestCase {
                name: "very large",
                input: Time::seconds(i64::from(i32::MAX) * 3500),
                expected: "2087831323:28:20".to_string(),
            },
            TestCase {
                name: "MAX",
                input: Time::MAX,
                expected: "2562047788015:12:55.807".to_string(),
            },
            TestCase {
                name: "i16::MIN",
                input: Time::seconds(i64::from(i16::MIN)),
                expected: "-09:06:08".to_string(),
            },
            TestCase {
                name: "i64::MIN",
                input: Time::millis(i64::MIN),
                expected: "-2562047788015:12:55.808".to_string(),
            },
            TestCase {
                name: "millis",
                input: Time::hours(3) + Duration::millis(42),
                expected: "03:00:00.042".to_string(),
            },
        ];
        for test in tests {
            assert_eq!(
                test.expected,
                format!("{:?}", test.input),
                "test '{}' failed",
                test.name
            );
        }
    }

    #[test]
    fn test_time_since_epoch() {
        let expected = Duration::seconds(3);
        let actual = Time::seconds(3).since_epoch();
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_time_from_duration() {
        let duration_pos = Duration::seconds(3);
        assert_eq!(Ok(Time::seconds(3)), Time::try_from(duration_pos));

        let duration_neg = Duration::seconds(-3);
        assert_eq!(
            Err("Duration cannot be negative."),
            Time::try_from(duration_neg)
        );
    }
}

#[cfg(test)]
mod duration_test {
    use super::*;

    #[test]
    fn duration_display() {
        assert_eq!("1ms", Duration::millis(1).to_string());
        assert_eq!("2s", Duration::seconds(2).to_string());
        assert_eq!("3m", Duration::minutes(3).to_string());
        assert_eq!("4h", Duration::hours(4).to_string());

        assert_eq!("1m1s", Duration::seconds(61).to_string());
        assert_eq!(
            "2h3m4s5ms",
            (Duration::hours(2)
                + Duration::minutes(3)
                + Duration::seconds(4)
                + Duration::millis(5))
            .to_string()
        );

        assert_eq!("0ms", Duration::ZERO.to_string());
        assert_eq!("-1m1s", Duration::seconds(-61).to_string());
    }

    #[test]
    fn test_time_window_display() {
        assert_eq!(
            "[1970-01-01T00:00:00+00:00, ∞]",
            TimeWindow::new(Time::EPOCH, Time::MAX).to_string()
        );
        assert_eq!(
            "[1970-01-01T01:00:00+00:00, 2024-02-06T16:53:47+00:00]",
            TimeWindow::new(Time::hours(1), Time::millis(1_707_238_427_962)).to_string()
        );
    }

    #[test]
    fn test_duration_is_non_negative_returns_correctly() {
        struct TestCase {
            name: &'static str,
            input: i64,
            expected: bool,
        }

        let tests = vec![
            TestCase {
                name: "negative",
                input: -1,
                expected: false,
            },
            TestCase {
                name: "zero",
                input: 0,
                expected: true,
            },
            TestCase {
                name: "positive",
                input: 1,
                expected: true,
            },
        ];

        for t in tests {
            let actual = Duration(t.input).is_non_negative();
            assert_eq!(t.expected, actual, "failed '{}'", t.name);
        }
    }

    #[test]
    fn test_duration_abs_removes_sign() {
        struct TestCase {
            name: &'static str,
            input: Duration,
            expected: Duration,
        }

        let tests = vec![
            TestCase {
                name: "negative",
                input: Duration::hours(-1),
                expected: Duration::hours(1),
            },
            TestCase {
                name: "zero",
                input: Duration::ZERO,
                expected: Duration::ZERO,
            },
            TestCase {
                name: "positive",
                input: Duration::minutes(1),
                expected: Duration::minutes(1),
            },
        ];

        for t in tests {
            let actual = t.input.abs();
            assert_eq!(t.expected, actual, "failed '{}'", t.name);
        }
    }

    #[test]
    fn test_duration_is_positive_returns_correctly() {
        struct TestCase {
            name: &'static str,
            input: i64,
            expected: bool,
        }

        let tests = vec![
            TestCase {
                name: "negative",
                input: -1,
                expected: false,
            },
            TestCase {
                name: "zero",
                input: 0,
                expected: false,
            },
            TestCase {
                name: "positive",
                input: 1,
                expected: true,
            },
        ];

        for t in tests {
            let actual = Duration(t.input).is_positive();
            assert_eq!(t.expected, actual, "failed '{}'", t.name);
        }
    }

    #[test]
    fn time_add_duration() {
        let mut time = Time::millis(1);
        let expected_time = Time::millis(3);
        let duration = Duration::millis(2);
        //  add
        assert_eq!(expected_time, time + duration);
        // add assign
        time += duration;
        assert_eq!(expected_time, time);
    }

    #[test]
    fn time_sub_duration() {
        let mut time = Time::millis(10);
        let expected_time = Time::millis(3);
        let duration = Duration::millis(7);
        // small time: sub
        assert_eq!(expected_time, time - duration);
        // small time: sub assign
        time -= duration;
        assert_eq!(expected_time, time);
    }

    #[test]
    fn time_sub_time() {
        // small numbers
        let time = Time::minutes(7);
        let time2 = Time::minutes(3);
        assert_eq!(Duration::minutes(4), time - time2);
        assert_eq!(Duration::minutes(-4), time2 - time);
    }

    #[test]
    fn time_rem_duration() {
        let time57 = Time::minutes(57);
        assert_eq!(Duration::ZERO, time57 % Duration::minutes(1));
        assert_eq!(Duration::minutes(57), time57 % Duration::minutes(60));
        assert_eq!(
            Duration::minutes(57),
            (time57 + Duration::hours(17)) % Duration::minutes(60)
        );
    }

    #[test]
    fn duration_rem_duration() {
        let dur34 = Duration::minutes(34);
        assert_eq!(Duration::ZERO, dur34 % Duration::minutes(1));
        assert_eq!(Duration::minutes(34), dur34 % Duration::minutes(45));
        assert_eq!(Duration::minutes(10), dur34 % Duration::minutes(12));
    }

    #[test]
    fn duration_rem_assign_duration() {
        let mut dur = Duration::minutes(734);
        dur %= Duration::minutes(100);
        assert_eq!(Duration::minutes(34), dur);
    }
}
