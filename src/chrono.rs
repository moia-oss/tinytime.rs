use core::fmt;
use std::fmt::Display;
use std::fmt::Formatter;

use chrono::DateTime;
use chrono::format::DelayedFormat;
use chrono::format::StrftimeItems;

use crate::Time;
use crate::TimeWindow;
impl Time {
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
    #[must_use]
    pub fn format<'a>(&self, fmt: &'a str) -> DelayedFormat<StrftimeItems<'a>> {
        let secs = self.0 / 1000;
        let nanos = (self.0 % 1000) * 1_000_000;
        #[expect(
            clippy::cast_possible_truncation,
            reason = "casting to u32 is safe here because it is guaranteed that the value is in 0..1_000_000_000"
        )]
        let nanos = if nanos.is_negative() {
            1_000_000_000 - nanos.unsigned_abs()
        } else {
            nanos.unsigned_abs()
        } as u32;

        let t = DateTime::from_timestamp(secs, nanos);
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
    /// For using this with `serde`, see [`Time::deserialize_rfc3339()`].
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
            .map(|chrono_datetime| Time::millis(chrono_datetime.timestamp_millis()))
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
    #[must_use]
    pub fn to_rfc3339(self) -> String {
        self.format("%Y-%m-%dT%H:%M:%S+00:00").to_string()
    }
}

impl Display for Time {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let rfc3339_string = self.to_rfc3339();
        write!(f, "{rfc3339_string}")
    }
}

impl Display for TimeWindow {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "[{}, {}]", self.start, self.end)
    }
}
