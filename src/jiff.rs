use core::fmt;
use std::fmt::Display;
use std::fmt::Formatter;

use ::jiff::SignedDuration;
use ::jiff::Timestamp;
use ::jiff::fmt::strtime;

use crate::Duration;
use crate::Time;
use crate::TimeWindow;

const RFC3339_FORMAT: &str = "%Y-%m-%dT%H:%M:%S+00:00";

/// A displayable formatted [`Time`].
pub struct FormattedTime<'a> {
    inner: FormattedTimeInner<'a>,
}

enum FormattedTimeInner<'a> {
    Finite(strtime::Display<'a>),
    PlusInfinity,
    MinusInfinity,
}

impl fmt::Debug for FormattedTime<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl Display for FormattedTime<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match &self.inner {
            FormattedTimeInner::Finite(value) => Display::fmt(value, f),
            FormattedTimeInner::PlusInfinity => f.write_str("∞"),
            FormattedTimeInner::MinusInfinity => f.write_str("-∞"),
        }
    }
}

impl Time {
    /// The function format string is forwarded to
    /// [`jiff::Timestamp::strftime()`].
    ///
    /// Values outside jiff's timestamp range, such as `Time::MAX`, are
    /// formatted as "∞" or "-∞".
    ///
    /// # Example
    ///
    /// ```
    /// use tinytime::Time;
    /// assert_eq!("∞", Time::MAX.format("whatever").to_string());
    /// assert_eq!("-∞", Time::millis(i64::MIN).format("whatever").to_string());
    /// ```
    #[must_use]
    pub fn format<'a>(&self, fmt: &'a str) -> FormattedTime<'a> {
        let inner = match Timestamp::from_millisecond(self.0) {
            Ok(timestamp) => FormattedTimeInner::Finite(timestamp.strftime(fmt)),
            Err(_) => {
                if self.0.is_positive() {
                    FormattedTimeInner::PlusInfinity
                } else {
                    FormattedTimeInner::MinusInfinity
                }
            }
        };

        FormattedTime { inner }
    }

    /// Parses an RFC 3339 date and time string into a [Time] instance.
    ///
    /// The parsing is forwarded to [`jiff::Timestamp`].
    /// Note that any time smaller than milliseconds is truncated.
    ///
    /// For using this with `serde`, see [`Time::deserialize_rfc3339()`].
    ///
    /// ## Example
    /// ```
    /// use tinytime::Duration;
    /// use tinytime::Time;
    /// assert_eq!(
    ///     Time::hours(2) + Duration::minutes(51) + Duration::seconds(7) + Duration::millis(123),
    ///     Time::parse_from_rfc3339("1970-01-01T02:51:07.123999Z").unwrap()
    /// );
    /// ```
    pub fn parse_from_rfc3339(s: &str) -> Result<Time, jiff::Error> {
        s.parse::<Timestamp>()
            .map(|timestamp| Time::millis(timestamp.as_millisecond()))
    }

    /// Returns an RFC 3339 and ISO 8601 date and time string such as
    /// 1996-12-19T16:39:57+00:00.
    ///
    /// Values outside jiff's timestamp range, such as `Time::MAX`, are
    /// formatted as "∞" or "-∞".
    ///
    /// # Example
    ///
    /// ```
    /// use tinytime::Time;
    /// assert_eq!("∞", Time::MAX.to_rfc3339());
    /// assert_eq!("-∞", Time::millis(i64::MIN).to_rfc3339());
    /// ```
    #[must_use]
    pub fn to_rfc3339(self) -> String {
        self.format(RFC3339_FORMAT).to_string()
    }
}

impl Display for Time {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        Display::fmt(&self.format(RFC3339_FORMAT), f)
    }
}

impl Display for TimeWindow {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "[{}, {}]", self.start, self.end)
    }
}

impl From<Timestamp> for Time {
    fn from(timestamp: Timestamp) -> Self {
        Time::millis(timestamp.as_millisecond())
    }
}

impl From<SignedDuration> for Duration {
    fn from(duration: SignedDuration) -> Self {
        let millis = duration.as_millis();
        let millis_conv_result = i64::try_from(millis);
        debug_assert!(
            millis_conv_result.is_ok(),
            "Input jiff::SignedDuration ({duration:?}) is too large to be converted to tinytime::Duration"
        );
        Duration::millis(millis_conv_result.unwrap_or(if millis < 0 { i64::MIN } else { i64::MAX }))
    }
}
