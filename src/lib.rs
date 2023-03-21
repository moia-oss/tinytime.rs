#![allow(rustdoc::private_intra_doc_links)]
#![deny(rustdoc::broken_intra_doc_links)]
#![warn(clippy::disallowed_types)]
//! Low overhead implementation of time related concepts.
use core::fmt;
use std::cmp::max;
use std::cmp::Ordering;
use std::error::Error;
use std::fmt::Debug;
use std::fmt::Display;
use std::ops::Add;
use std::ops::AddAssign;
use std::ops::Div;
use std::ops::Mul;
use std::ops::MulAssign;
use std::ops::Sub;
use std::ops::SubAssign;
use std::str::FromStr;

use chrono::format::DelayedFormat;
use chrono::format::StrftimeItems;
use chrono::DateTime;
use chrono::NaiveDateTime;
use derive_more::Deref;
use derive_more::From;
use derive_more::Into;
use derive_more::Neg;
use derive_more::Sum;
use lazy_static::lazy_static;
use regex::Regex;
use serde::de::Visitor;
use serde::Deserialize;
use serde::Serialize;

/// A point in time.
///
/// Low overhead time representation. Cannot be negative. Internally represented
/// as milliseconds.
#[derive(
    Eq, PartialEq, Hash, Ord, PartialOrd, Copy, Clone, Debug, Default, Serialize, Deref, From, Into,
)]
pub struct Time(usize);
impl Time {
    pub const MAX: Self = Self(usize::MAX);
    pub const EPOCH: Self = Self(0_usize);

    const SECOND: Time = Time(1000);
    const MINUTE: Time = Time(60 * Self::SECOND.0);
    const HOUR: Time = Time(60 * Self::MINUTE.0);

    pub const fn millis(millis: usize) -> Self {
        Time(millis)
    }

    pub const fn seconds(seconds: usize) -> Self {
        Time::millis(seconds * Self::SECOND.0)
    }

    pub const fn minutes(minutes: usize) -> Self {
        Time::millis(minutes * Self::MINUTE.0)
    }

    pub const fn hours(hours: usize) -> Self {
        Time::millis(hours * Self::HOUR.0)
    }

    /// Returns an RFC 3339 and ISO 8601 date and time string such as
    /// 1996-12-19T16:39:57+00:00.
    ///
    /// Values above ~240148-08-31, such as `Time::MAX` are formatted as "∞"
    ///
    /// # Example
    ///
    /// ```
    /// use tinytime::Time;
    /// assert_eq!("∞", Time::MAX.to_rfc3339());
    /// ```
    pub fn to_rfc3339(self) -> String {
        self.format("%Y-%m-%dT%H:%M:%S+00:00").to_string()
    }

    /// The function format string is forwarded to
    /// [`chrono::NaiveDateTime::format()`]
    ///
    /// Values above ~240148-08-31, such as `Time::MAX` are formatted as "∞"
    ///
    /// # Example
    ///
    /// ```
    /// use tinytime::Time;
    /// assert_eq!("∞", Time::MAX.format("whatever").to_string());
    /// ```
    pub fn format<'a>(&self, fmt: &'a str) -> DelayedFormat<StrftimeItems<'a>> {
        let secs = self.0 / 1000;
        let nanos = (self.0 % 1000) * 1_000_000;
        let t = NaiveDateTime::from_timestamp_opt(secs as i64, nanos as u32);
        match t {
            None => DelayedFormat::new(None, None, StrftimeItems::new("∞")),
            Some(v) => v.format(fmt),
        }
    }

    /// Parses an RFC 3339 date and time string into a [Time] instance.
    ///
    /// The parsing is forwarded to [`chrono::DateTime::parse_from_rfc3339()`].
    /// Note that any time smaller than milliseconds is truncated.
    ///
    /// ## Example
    /// ```
    /// use tinytime::Duration;
    /// use tinytime::Time;
    /// assert_eq!(
    ///     Ok(Time::hours(2) + Duration::minutes(51) + Duration::seconds(7) + Duration::millis(123)),
    ///     Time::parse_from_rfc3339("1970-01-01T02:51:07.123999Z")
    /// );
    /// ```
    pub fn parse_from_rfc3339(s: &str) -> Result<Time, chrono::ParseError> {
        DateTime::parse_from_rfc3339(s)
            .map(|chrono_datetime| Time::millis(chrono_datetime.timestamp_millis() as usize))
    }

    /// Returns the current time instance.
    ///
    /// Don't use this method to compare if the current time has passed a
    /// certain deadline.
    pub fn now() -> Time {
        Time::millis(chrono::Local::now().timestamp_millis() as usize)
    }

    pub fn as_millis(&self) -> usize {
        self.0
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
    pub fn round_down(&self, step_size: Duration) -> Time {
        let time_milli = self.as_millis();
        let part = time_milli % step_size.as_millis_unsigned();
        Time::millis(time_milli - part)
    }

    /// Rounds time uo to a step size
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
    pub fn round_up(&self, step_size: Duration) -> Time {
        let time_milli = self.as_millis();
        let step_milli = step_size.as_millis_unsigned();
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
    pub fn checked_sub(&self, rhs: Duration) -> Option<Self> {
        // check for overflow
        if Time::EPOCH + rhs > *self {
            None
        } else {
            Some(*self - rhs)
        }
    }

    pub fn since_epoch(&self) -> Duration {
        debug_assert!(isize::try_from(self.0).is_ok());
        Duration::millis(self.as_millis() as isize)
    }
}

/// Allows deserializing from RFC 3339 strings and unsigned integers.
impl<'de> Deserialize<'de> for Time {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        deserializer.deserialize_any(TimeVisitor)
    }
}

struct TimeVisitor;
impl<'de> Visitor<'de> for TimeVisitor {
    type Value = Time;

    fn expecting(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
        formatter.write_str("either a Time newtype, an RFC 3339 string, or an unsigned integer indicating epoch milliseconds")
    }

    fn visit_str<E>(self, v: &str) -> Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        Time::parse_from_rfc3339(v).map_err(|e| E::custom(e.to_string()))
    }

    fn visit_u64<E>(self, v: u64) -> Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        usize::try_from(v)
            .map_err(|e| E::custom(e.to_string()))
            .map(Time::millis)
    }

    fn visit_newtype_struct<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        // expecting an unsigned integer inside the newtype struct, but technically also
        // allowing strings
        deserializer.deserialize_newtype_struct("Time", Self)
    }
}

impl From<Time> for std::time::SystemTime {
    fn from(input: Time) -> Self {
        std::time::UNIX_EPOCH + std::time::Duration::from_millis(input.0 as u64)
    }
}

/// An interval or range of time: `[start,end)`.
#[derive(Clone, Debug, Eq, PartialEq, Default, Copy, Serialize, Deserialize, From, Into)]
pub struct TimeWindow {
    start: Time,
    end: Time,
}

impl TimeWindow {
    pub fn new(start: Time, end: Time) -> Self {
        debug_assert!(start <= end);
        debug_assert!(
            end.0 - start.0 <= Duration::MAX.0 as usize,
            "The difference between time window start {start:?} and end {end:?} is bigger than Duration::MAX"
        );
        TimeWindow { start, end }
    }

    /// Returns [`TimeWindow`] with range [[`Time::EPOCH`], `end`)
    pub fn epoch_to(end: Time) -> Self {
        Self::new(Time::EPOCH, end)
    }

    pub fn from_minutes(a: usize, b: usize) -> Self {
        TimeWindow::new(Time::minutes(a), Time::minutes(b))
    }

    pub fn from_seconds(a: usize, b: usize) -> Self {
        TimeWindow::new(Time::seconds(a), Time::seconds(b))
    }

    /// Creates time window from start time and duration.
    /// # Examples
    ///
    /// ```
    /// # use tinytime::Duration;
    /// # use tinytime::Time;
    /// # use tinytime::TimeWindow;
    /// let mut x = TimeWindow::from_duration(Time::seconds(1), Duration::seconds(2));
    /// assert_eq!(Time::seconds(1), x.start());
    /// assert_eq!(Time::seconds(3), x.end());
    /// ```
    pub fn from_duration(start: Time, duration: Duration) -> Self {
        TimeWindow {
            start,
            end: start.add(duration),
        }
    }

    pub const fn instant(time: Time) -> Self {
        TimeWindow {
            start: time,
            end: time,
        }
    }

    pub fn widest() -> Self {
        TimeWindow {
            start: Time::EPOCH,
            end: Time::EPOCH + Duration::MAX,
        }
    }

    pub fn instant_seconds(seconds: usize) -> Self {
        TimeWindow::from_seconds(seconds, seconds)
    }

    pub const fn start(&self) -> Time {
        self.start
    }

    pub const fn end(&self) -> Time {
        self.end
    }

    pub fn duration(&self) -> Duration {
        self.end - self.start
    }

    pub fn set_start(&mut self, start: Time) {
        debug_assert!(start <= self.end);
        self.start = start;
    }

    pub fn set_end(&mut self, end: Time) {
        debug_assert!(self.start <= end);
        self.end = end;
    }

    /// Extends time window end to the given value. Is a No-Op when given value
    /// isn't greater than current time window end.
    /// Returns by which duration the deadline was extended.
    /// # Examples
    ///
    /// ```
    /// # use tinytime::Duration;
    /// # use tinytime::Time;
    /// # use tinytime::TimeWindow;
    /// let mut x = TimeWindow::from_seconds(1, 2);
    /// assert_eq!(Some(Duration::seconds(1)), x.extend_end(Time::seconds(3)));
    /// assert_eq!(Time::seconds(3), x.end());
    /// assert_eq!(None, x.extend_end(Time::EPOCH));
    /// assert_eq!(Time::seconds(3), x.end());
    /// ```
    pub fn extend_end(&mut self, new_end: Time) -> Option<Duration> {
        if new_end > self.end {
            let diff = new_end - self.end;
            self.set_end(new_end);
            Some(diff)
        } else {
            None
        }
    }

    /// Extends time window end by the given duration.
    ///
    /// # Examples
    ///
    /// ```
    /// # use tinytime::Duration;
    /// # use tinytime::Time;
    /// # use tinytime::TimeWindow;
    /// let mut x = TimeWindow::from_seconds(1, 2);
    /// assert_eq!(
    ///     Time::seconds(5),
    ///     x.extend_end_by(Duration::seconds(3)).end()
    /// );
    /// ```
    pub fn extend_end_by(&self, duration: Duration) -> TimeWindow {
        TimeWindow {
            start: self.start,
            end: self.end + duration,
        }
    }

    /// Postpones the time window start to the given value. Is a No-Op when
    /// given value isn't greater than current time window start. Will never
    /// postpone the start past the end of the time window.
    /// # Examples
    ///
    /// ```
    /// # use tinytime::Time;
    /// # use tinytime::TimeWindow;
    /// let mut x = TimeWindow::from_seconds(1, 3);
    /// x.shrink_towards_end(Time::EPOCH);
    /// assert_eq!(Time::seconds(1), x.start());
    /// x.shrink_towards_end(Time::seconds(2));
    /// assert_eq!(Time::seconds(2), x.start());
    /// x.shrink_towards_end(Time::seconds(4));
    /// assert_eq!(Time::seconds(3), x.start());
    /// ```
    pub fn shrink_towards_end(&mut self, new_start: Time) {
        if new_start > self.start {
            if new_start > self.end {
                self.set_start(self.end);
            } else {
                self.set_start(new_start);
            }
        }
    }

    /// Prepones the time window end to the given value. May be a No-Op.
    /// Will never prepone the end more than to the start of the time window.
    /// # Examples
    ///
    /// ```
    /// # use tinytime::Time;
    /// # use tinytime::TimeWindow;
    /// let mut x = TimeWindow::from_seconds(1, 3);
    /// x.shrink_towards_start(Time::seconds(4));
    /// assert_eq!(Time::seconds(3), x.end());
    /// x.shrink_towards_start(Time::seconds(2));
    /// assert_eq!(Time::seconds(2), x.end());
    /// x.shrink_towards_start(Time::EPOCH);
    /// assert_eq!(Time::seconds(1), x.end());
    /// ```
    pub fn shrink_towards_start(&mut self, new_end: Time) {
        if new_end < self.end {
            if new_end < self.start {
                self.set_end(self.start);
            } else {
                self.set_end(new_end);
            }
        }
    }

    /// Returns true if this time window overlaps with another one
    /// # Examples
    ///
    /// ```
    /// # use tinytime::Time;
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
    pub fn overlaps(&self, that: &TimeWindow) -> bool {
        self.start < that.end && that.start < self.end
    }
}

/// A duration of time.
///
/// Duration can be negative. Internally duration is represented as
/// milliseconds.
#[derive(
    Eq,
    PartialEq,
    Ord,
    PartialOrd,
    Copy,
    Clone,
    Debug,
    Default,
    Hash,
    Serialize,
    Deref,
    From,
    Into,
    Sum,
    Neg,
)]
pub struct Duration(isize);

impl Duration {
    pub const ZERO: Self = Self(0_isize);
    pub const MAX: Self = Self(isize::MAX);

    const SECOND: Duration = Duration(1000);
    const MINUTE: Duration = Duration(60 * Self::SECOND.0);
    const HOUR: Duration = Duration(60 * Self::MINUTE.0);

    /// Create a duration instance from hours
    pub const fn hours(hours: isize) -> Self {
        Duration(hours * Self::HOUR.0)
    }

    /// Create a duration instance from minutes.
    pub const fn minutes(minutes: isize) -> Self {
        Duration(minutes * Self::MINUTE.0)
    }

    /// Create a duration instance from seconds.
    pub const fn seconds(seconds: isize) -> Self {
        Duration(seconds * Self::SECOND.0)
    }

    /// Create a duration instance from ms.
    pub const fn millis(ms: isize) -> Self {
        Duration(ms)
    }

    pub fn abs(&self) -> Self {
        if self >= &Duration::ZERO {
            *self
        } else {
            -*self
        }
    }
    /// Returns the number of whole milliseconds in the Duration instance.
    pub fn as_millis(&self) -> isize {
        self.0
    }

    /// Returns the number of non-negative whole milliseconds in the Duration
    /// instance.
    pub fn as_millis_unsigned(&self) -> usize {
        max(self.0, 0) as usize
    }

    /// Returns the number of whole seconds in the Duration instance.
    pub const fn as_seconds(&self) -> isize {
        self.0 / Self::SECOND.0
    }

    /// Returns the number of non-negative whole seconds in the Duration
    /// instance.
    pub fn as_seconds_unsigned(&self) -> usize {
        max(0, self.0 / 1000) as usize
    }

    /// Returns the number of whole minutes in the Duration instance.
    pub const fn as_minutes(&self) -> isize {
        self.0 / Self::MINUTE.0
    }

    /// Returns true if duration is `>= 0`.
    pub const fn is_non_negative(&self) -> bool {
        self.0 >= 0
    }

    /// Returns true if duration is `> 0`.
    pub const fn is_positive(&self) -> bool {
        self.0 > 0
    }
}

/// Allows deserializing from strings, unsigned integers, and signed integers.
impl<'de> Deserialize<'de> for Duration {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        deserializer.deserialize_any(DurationVisitor)
    }
}

impl PartialEq<std::time::Duration> for Duration {
    fn eq(&self, other: &std::time::Duration) -> bool {
        (self.as_millis_unsigned() as u128).eq(&other.as_millis())
    }
}

impl PartialOrd<std::time::Duration> for Duration {
    fn partial_cmp(&self, other: &std::time::Duration) -> Option<Ordering> {
        (self.as_millis_unsigned() as u128).partial_cmp(&other.as_millis())
    }
}

struct DurationVisitor;
impl<'de> Visitor<'de> for DurationVisitor {
    type Value = Duration;

    fn expecting(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
        formatter.write_str(
            "either a Duration newtype, an (signed or unsigned) integer indicating milliseconds, or a duration string",
        )
    }

    fn visit_str<E>(self, v: &str) -> Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        Duration::from_str(v).map_err(|e| E::custom(e.to_string()))
    }

    fn visit_u64<E>(self, v: u64) -> Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        isize::try_from(v)
            .map_err(|e| E::custom(e.to_string()))
            .map(Duration::millis)
    }

    fn visit_i64<E>(self, v: i64) -> Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        isize::try_from(v)
            .map_err(|e| E::custom(e.to_string()))
            .map(Duration::millis)
    }

    fn visit_newtype_struct<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        // expecting a signed integer inside the newtype struct, but technically also
        // allowing strings and signed integers
        deserializer.deserialize_newtype_struct("Duration", Self)
    }
}

impl Display for Duration {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
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

impl From<f64> for Duration {
    fn from(num: f64) -> Self {
        Duration::millis(num as isize)
    }
}

impl TryFrom<Duration> for Time {
    type Error = &'static str;
    fn try_from(duration: Duration) -> Result<Self, Self::Error> {
        if duration.is_non_negative() {
            Ok(Time::millis(duration.as_millis() as usize))
        } else {
            Err("Duration cannot be negative.")
        }
    }
}

impl From<Duration> for f64 {
    fn from(num: Duration) -> Self {
        num.0 as f64
    }
}

impl AddAssign<Time> for Time {
    fn add_assign(&mut self, rhs: Time) {
        debug_assert!(
            self.0.checked_add(rhs.0).is_some(),
            "overflow detected: {self:?} += {rhs:?}"
        );
        self.0 += rhs.0;
    }
}

impl AddAssign<Duration> for Time {
    fn add_assign(&mut self, rhs: Duration) {
        if rhs.is_negative() {
            debug_assert!(
                self.0.checked_sub(rhs.0.unsigned_abs()).is_some(),
                "overflow detected: {self:?} + {rhs:?}"
            );
            self.0 -= rhs.0.unsigned_abs();
        } else {
            debug_assert!(
                self.0.checked_add(rhs.0.unsigned_abs()).is_some(),
                "overflow detected: {self:?} + {rhs:?}"
            );
            self.0 += rhs.0.unsigned_abs();
        }
    }
}

impl Add<Duration> for Time {
    type Output = Time;

    fn add(self, rhs: Duration) -> Self::Output {
        if rhs.is_negative() {
            debug_assert!(
                self.0.checked_sub(rhs.0.unsigned_abs()).is_some(),
                "overflow detected: {self:?} + {rhs:?}"
            );
            Time(self.0 - rhs.0.unsigned_abs())
        } else {
            debug_assert!(
                self.0.checked_add(rhs.0.unsigned_abs()).is_some(),
                "overflow detected: {self:?} + {rhs:?}"
            );
            Time(self.0 + rhs.0.unsigned_abs())
        }
    }
}

impl Sub<Duration> for Time {
    type Output = Time;

    fn sub(self, rhs: Duration) -> Self::Output {
        if rhs.is_negative() {
            debug_assert!(
                self.0.checked_add(rhs.0.unsigned_abs()).is_some(),
                "overflow detected: {self:?} + {rhs:?}"
            );
            Time(self.0 + rhs.0.unsigned_abs())
        } else {
            debug_assert!(
                self.0.checked_sub(rhs.0.unsigned_abs()).is_some(),
                "overflow detected: {self:?} + {rhs:?}"
            );
            Time(self.0 - rhs.0.unsigned_abs())
        }
    }
}

impl SubAssign<Duration> for Time {
    fn sub_assign(&mut self, rhs: Duration) {
        if rhs.is_negative() {
            debug_assert!(
                self.0.checked_add(rhs.0.unsigned_abs()).is_some(),
                "overflow detected: {self:?} + {rhs:?}"
            );
            self.0 += rhs.0.unsigned_abs();
        } else {
            debug_assert!(
                self.0.checked_sub(rhs.0.unsigned_abs()).is_some(),
                "overflow detected: {self:?} + {rhs:?}"
            );
            self.0 -= rhs.0.unsigned_abs()
        }
    }
}

impl Sub<Time> for Time {
    type Output = Duration;

    fn sub(self, rhs: Time) -> Self::Output {
        if self > rhs {
            debug_assert!(
                isize::try_from(self.0 - rhs.0).is_ok(),
                "Overflow detected, Time instances are too far apart: {self:?} - {rhs:?}"
            );
            Duration((self.0 - rhs.0) as isize)
        } else {
            debug_assert!(
                isize::try_from(rhs.0 - self.0).is_ok(),
                "Overflow detected, Time instances are too far apart: {self:?} - {rhs:?}"
            );
            Duration(-((rhs.0 - self.0) as isize))
        }
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

impl SubAssign<Duration> for Duration {
    fn sub_assign(&mut self, rhs: Duration) {
        debug_assert!(
            self.0.checked_sub(rhs.0).is_some(),
            "overflow detected: {self:?} -= {rhs:?}"
        );
        self.0 -= rhs.0;
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

impl Mul<isize> for Duration {
    type Output = Duration;

    fn mul(self, rhs: isize) -> Self::Output {
        debug_assert!(
            self.0.checked_mul(rhs).is_some(),
            "overflow detected: {self:?} * {rhs:?}"
        );
        Duration(self.0 * rhs)
    }
}

impl MulAssign<isize> for Duration {
    fn mul_assign(&mut self, rhs: isize) {
        debug_assert!(
            self.0.checked_mul(rhs).is_some(),
            "overflow detected: {self:?} *= {rhs:?}"
        );
        self.0 *= rhs
    }
}

impl Mul<Duration> for isize {
    type Output = Duration;

    fn mul(self, rhs: Duration) -> Self::Output {
        debug_assert!(
            self.checked_mul(rhs.0).is_some(),
            "overflow detected: {self:?} * {rhs:?}"
        );
        Duration(self * rhs.0)
    }
}

impl Mul<f64> for Duration {
    type Output = Duration;

    fn mul(self, rhs: f64) -> Self::Output {
        Duration((self.0 as f64 * rhs).round() as isize)
    }
}

impl Mul<Duration> for f64 {
    type Output = Duration;

    fn mul(self, rhs: Duration) -> Self::Output {
        rhs * self
    }
}

// Returns rounded Duration
impl Div<f64> for Duration {
    type Output = Duration;

    fn div(self, rhs: f64) -> Self::Output {
        debug_assert_ne!(
            rhs, 0.0,
            "Dividing by zero results in INF. This is probably not what you want."
        );
        Duration((self.0 as f64 / rhs).round() as isize)
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

impl From<Duration> for std::time::Duration {
    fn from(input: Duration) -> Self {
        let secs = input.0 / 1000;
        let nanos = (input.0 % 1000) * 1_000_000;
        std::time::Duration::new(secs as u64, nanos as u32)
    }
}
impl From<std::time::Duration> for Duration {
    fn from(input: std::time::Duration) -> Self {
        Duration::millis(input.as_millis() as isize)
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

    fn from_str(seconds: &str) -> Result<Self, Self::Err> {
        lazy_static! {
            static ref RE: Regex = Regex::new(REGEX).unwrap();
        }
        let captures = RE
            .captures(seconds)
            .ok_or(DurationParseError::UnrecognizedFormat)?;
        let mut duration = Duration::ZERO;
        if let Some(h) = captures.name("h") {
            duration += Duration::hours(h.as_str().parse::<isize>().unwrap());
        }
        if let Some(m) = captures.name("m") {
            duration += Duration::minutes(m.as_str().parse::<isize>().unwrap());
        }
        if let Some(s) = captures.name("s") {
            duration += Duration::seconds(s.as_str().parse::<isize>().unwrap());
        }
        if let Some(ms) = captures.name("ms") {
            duration += Duration::millis(ms.as_str().parse::<isize>().unwrap());
        }
        if captures.name("sign").is_some() {
            duration *= -1;
        }
        Ok(duration)
    }
}

#[derive(Debug)]
pub enum DurationParseError {
    UnrecognizedFormat,
}
impl Error for DurationParseError {}

impl Display for DurationParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "Unrecognized Duration format, valid examples are '2h3s', '1m', '1h3m5s700ms'"
        )
    }
}

const REGEX: &str = r"^(?P<sign>-)?((?P<h>\d+)h)?((?P<m>\d+)m)?((?P<s>\d+)s)?((?P<ms>\d+)ms)?$";

#[cfg(test)]
mod time_test {
    use serde_test::assert_de_tokens;
    use serde_test::Token;

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
                name: "i32::MAX + 1",
                input: Time::seconds(i32::MAX as usize + 1),
                expected: "2038-01-19T03:14:08+00:00".to_string(),
            },
            TestCase {
                name: "u32::MAX + 1",
                input: Time::seconds(u32::MAX as usize + 1),
                expected: "2106-02-07T06:28:16+00:00".to_string(),
            },
            TestCase {
                name: "very large",
                input: Time::seconds(i32::MAX as usize * 3500),
                expected: "+240148-08-31T19:28:20+00:00".to_string(),
            },
            TestCase {
                name: "MAX",
                input: Time::MAX,
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
    fn deserialize_time() {
        // strings
        assert_de_tokens(&Time::seconds(7), &[Token::Str("1970-01-01T00:00:07Z")]);
        assert_de_tokens(&Time::seconds(7), &[Token::String("1970-01-01T00:00:07Z")]);
        assert_de_tokens(
            &Time::seconds(7),
            &[Token::BorrowedStr("1970-01-01T00:00:07Z")],
        );

        // unsigned integers
        assert_de_tokens(&Time::millis(7), &[Token::U8(7)]);
        assert_de_tokens(&Time::millis(65_535), &[Token::U16(65_535)]);
        assert_de_tokens(&Time::hours(10), &[Token::U32(36_000_000)]);
        assert_de_tokens(&Time::hours(100), &[Token::U64(360_000_000)]);

        assert_de_tokens(
            &Time::hours(1),
            &[Token::NewtypeStruct { name: "Time" }, Token::U64(3_600_000)],
        );

        // unsigned integer
        assert_eq!(
            Time::EPOCH + Duration::millis(1000),
            serde_json::from_str("1000").unwrap()
        );

        // RFC 3339
        assert_eq!(
            Time::EPOCH + Duration::hours(12) + Duration::minutes(1),
            serde_json::from_str("\"1970-01-01T12:01:00Z\"").unwrap()
        );

        // ser-de
        let time = Time::EPOCH + Duration::hours(48) + Duration::minutes(7);
        let json = serde_json::to_string(&time).unwrap();
        assert_eq!(time, serde_json::from_str(json.as_str()).unwrap());
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
    use serde_test::assert_de_tokens;
    use serde_test::Token;

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
    fn test_duration_is_non_negative_returns_correctly() {
        struct TestCase {
            name: &'static str,
            input: isize,
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
            input: isize,
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
        let mut small_time = Time::millis(1);
        let expected_time = Time::millis(3);
        let duration = Duration::millis(2);
        // small time: add
        assert_eq!(expected_time, small_time + duration);
        // small time: add assign
        small_time += duration;
        assert_eq!(expected_time, small_time);

        let mut big_time = Time::hours(2_600_000_000_000);
        assert!(big_time > Time::EPOCH + Duration::MAX);
        // big time: add
        assert_eq!(
            Time::hours(2_600_000_000_010),
            big_time + Duration::hours(10)
        );
        // big time: add assign
        big_time += Duration::hours(10);
        assert_eq!(Time::hours(2_600_000_000_010), big_time);
    }

    #[test]
    fn time_sub_duration() {
        let mut small_time = Time::millis(10);
        let expected_time = Time::millis(3);
        let duration = Duration::millis(7);
        // small time: sub
        assert_eq!(expected_time, small_time - duration);
        // small time: sub assign
        small_time -= duration;
        assert_eq!(expected_time, small_time);

        let mut big_time = Time::hours(2_600_000_000_010);
        assert!(big_time > Time::EPOCH + Duration::MAX);
        // big time: sub
        assert_eq!(
            Time::hours(2_600_000_000_002),
            big_time - Duration::hours(8)
        );
        // big time: sub assign
        big_time -= Duration::hours(8);
        assert_eq!(Time::hours(2_600_000_000_002), big_time);
    }

    #[test]
    fn time_sub_time() {
        // small numbers
        let small_time = Time::minutes(7);
        let small_time2 = Time::minutes(3);
        assert_eq!(Duration::minutes(4), small_time - small_time2);
        assert_eq!(Duration::minutes(-4), small_time2 - small_time);

        // big numbers
        let big_time = Time::hours(2_600_000_000_000);
        let big_time2 = Time::hours(2_600_000_000_012);
        assert_eq!(Duration::hours(-12), big_time - big_time2);
        assert_eq!(Duration::hours(12), big_time2 - big_time);
    }

    #[test]
    fn deserialize_duration() {
        // strings
        assert_de_tokens(&Duration::minutes(7), &[Token::Str("7m")]);
        assert_de_tokens(
            &(Duration::minutes(7) + Duration::seconds(8)),
            &[Token::BorrowedStr("7m8s")],
        );
        assert_de_tokens(&Duration::hours(9), &[Token::String("9h")]);

        // unsigned integers
        assert_de_tokens(&Duration::millis(7), &[Token::U8(7)]);
        assert_de_tokens(&Duration::millis(65_535), &[Token::U16(65_535)]);
        assert_de_tokens(&Duration::hours(10), &[Token::U32(36_000_000)]);
        assert_de_tokens(&Duration::hours(100), &[Token::U64(360_000_000)]);

        // signed integers
        assert_de_tokens(&Duration::millis(-7), &[Token::I8(-7)]);
        assert_de_tokens(&Duration::millis(32_767), &[Token::I16(32_767)]);
        assert_de_tokens(&Duration::hours(10), &[Token::I32(36_000_000)]);
        assert_de_tokens(&Duration::hours(100), &[Token::I64(360_000_000)]);

        // newtype
        assert_de_tokens(
            &Duration::hours(1),
            &[
                Token::NewtypeStruct { name: "Duration" },
                Token::U64(3_600_000),
            ],
        );

        // integer
        let duration: Duration = serde_json::from_str("2").unwrap();
        assert_eq!(Duration::millis(2), duration);

        // signed integer
        let duration: Duration = serde_json::from_str("-2").unwrap();
        assert_eq!(Duration::millis(-2), duration);

        // duration string
        let duration: Duration = serde_json::from_str("\"3m4s\"").unwrap();
        assert_eq!(Duration::minutes(3) + Duration::seconds(4), duration);

        // negative duration string
        let duration: Duration = serde_json::from_str("\"-3m4s\"").unwrap();
        assert_eq!(Duration::minutes(-3) + Duration::seconds(-4), duration);

        // ser-de
        let expected = Duration::millis(77777);
        let json = serde_json::to_string(&expected).unwrap();
        let actual: Duration = serde_json::from_str(json.as_str()).unwrap();
        assert_eq!(expected, actual);
    }
}
