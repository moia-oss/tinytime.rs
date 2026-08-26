use core::fmt;
use std::fmt::Display;
use std::fmt::Formatter;
use std::num::TryFromIntError;

use ::jiff::SignedDuration;
use ::jiff::Timestamp;
use ::jiff::fmt::strtime;

use crate::Duration;
use crate::Time;
use crate::TimeWindow;

/// The representation of a [`Time`] that jiff cannot express.
const fn infinity(millis: i64) -> &'static str {
    if millis.is_negative() { "-∞" } else { "∞" }
}

/// Converts a millisecond count into a [`jiff::Timestamp`], if jiff can
/// represent it.
fn to_timestamp(millis: i64) -> Result<Timestamp, jiff::Error> {
    Timestamp::from_duration(SignedDuration::from_millis(millis))
}

impl Time {
    /// The function format string is forwarded to
    /// [`jiff::Timestamp::strftime()`].
    ///
    /// Values outside jiff's timestamp range, i.e. outside
    /// `-009999-01-02T01:59:59Z` to `9999-12-30T22:00:00.999Z`, such as
    /// `Time::MAX`, are formatted as "∞" or "-∞", ignoring the format string.
    ///
    /// # Panics
    ///
    /// The returned value panics when displayed if `fmt` isn't a format string
    /// that jiff supports. Note that jiff's set of `strftime` specifiers
    /// differs from chrono's: `%v` and `%+` are not supported, and `%Z` is
    /// emitted verbatim because a [`jiff::Timestamp`] carries no time zone.
    ///
    /// # Example
    ///
    /// ```
    /// use tinytime::Time;
    /// assert_eq!("∞", Time::MAX.format("whatever").to_string());
    /// assert_eq!("-∞", Time::millis(i64::MIN).format("whatever").to_string());
    /// ```
    #[must_use]
    pub fn format<'a>(&self, fmt: &'a str) -> strtime::Display<'a> {
        if let Ok(timestamp) = to_timestamp(self.0) {
            timestamp.strftime(fmt)
        } else {
            Timestamp::UNIX_EPOCH.strftime(infinity(self.0))
        }
    }

    /// Parses an RFC 3339 date and time string into a [Time] instance.
    ///
    /// The parsing is forwarded to the [`FromStr`](std::str::FromStr)
    /// implementation of [`jiff::Timestamp`].
    ///
    /// Any precision below milliseconds is truncated towards zero. For
    /// instants before the epoch that means the result is the millisecond
    /// *after* the parsed instant, e.g. "1969-12-31T23:59:59.999999Z" parses
    /// to [`Time::EPOCH`].
    #[cfg_attr(
        feature = "serde",
        doc = "\nFor using this with `serde`, see [`Time::deserialize_rfc3339()`].\n"
    )]
    /// ## Example
    /// ```
    /// use tinytime::Duration;
    /// use tinytime::Time;
    /// assert_eq!(
    ///     Time::hours(2) + Duration::minutes(51) + Duration::seconds(7) + Duration::millis(123),
    ///     Time::parse_from_rfc3339("1970-01-01T02:51:07.123999Z").unwrap()
    /// );
    /// assert_eq!(
    ///     Time::EPOCH,
    ///     Time::parse_from_rfc3339("1969-12-31T23:59:59.999999Z").unwrap()
    /// );
    /// ```
    pub fn parse_from_rfc3339(s: &str) -> Result<Time, jiff::Error> {
        s.parse::<Timestamp>()
            .map(|timestamp| Time::millis(timestamp.as_millisecond()))
    }

    /// Returns an RFC 3339 and ISO 8601 date and time string such as
    /// 1996-12-19T16:39:57Z.
    ///
    /// Formatting is forwarded to the [`Display`] implementation of
    /// [`jiff::Timestamp`], which renders UTC as "Z" and includes subsecond
    /// digits when they are non-zero.
    ///
    /// Values outside jiff's timestamp range, i.e. outside
    /// `-009999-01-02T01:59:59Z` to `9999-12-30T22:00:00.999Z`, such as
    /// `Time::MAX`, are formatted as "∞" or "-∞".
    ///
    /// # Example
    ///
    /// ```
    /// use tinytime::Time;
    /// assert_eq!(
    ///     "1996-12-19T16:39:57Z",
    ///     Time::seconds(851_013_597).to_rfc3339()
    /// );
    /// assert_eq!(
    ///     "2024-02-06T16:53:47.962Z",
    ///     Time::millis(1_707_238_427_962).to_rfc3339()
    /// );
    /// assert_eq!("∞", Time::MAX.to_rfc3339());
    /// assert_eq!("-∞", Time::millis(i64::MIN).to_rfc3339());
    /// ```
    #[must_use]
    pub fn to_rfc3339(self) -> String {
        self.to_string()
    }
}

impl Display for Time {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match to_timestamp(self.0) {
            Ok(timestamp) => Display::fmt(&timestamp, f),
            Err(_) => f.write_str(infinity(self.0)),
        }
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

impl TryFrom<SignedDuration> for Duration {
    type Error = TryFromIntError;

    /// Fails if the duration's milliseconds don't fit into an [`i64`].
    fn try_from(duration: SignedDuration) -> Result<Self, Self::Error> {
        i64::try_from(duration.as_millis()).map(Duration::millis)
    }
}

#[cfg(test)]
mod tests {
    use ::jiff::SignedDuration;
    use ::jiff::Timestamp;

    use crate::Duration;
    use crate::Time;
    use crate::TimeWindow;

    /// The last millisecond that jiff's `Timestamp` can represent.
    const LAST_FINITE_MILLIS: i64 = 253_402_207_200_999;

    /// The first millisecond that jiff's `Timestamp` can represent.
    const FIRST_FINITE_MILLIS: i64 = -377_705_023_201_000;

    struct DisplayTestCase {
        name: &'static str,
        input: Time,
        expected: &'static str,
        expected_format: &'static str,
    }

    fn display_test_cases() -> Vec<DisplayTestCase> {
        vec![
            DisplayTestCase {
                name: "EPOCH",
                input: Time::EPOCH,
                expected: "1970-01-01T00:00:00Z",
                expected_format: "1970-01-01T00:00:00+00:00",
            },
            DisplayTestCase {
                name: "i16::MAX + 1",
                input: Time::seconds(i64::from(i16::MAX) + 1),
                expected: "1970-01-01T09:06:08Z",
                expected_format: "1970-01-01T09:06:08+00:00",
            },
            DisplayTestCase {
                name: "i32::MAX + 1",
                input: Time::seconds(i64::from(i32::MAX) + 1),
                expected: "2038-01-19T03:14:08Z",
                expected_format: "2038-01-19T03:14:08+00:00",
            },
            DisplayTestCase {
                name: "u32::MAX + 1",
                input: Time::seconds(i64::from(u32::MAX) + 1),
                expected: "2106-02-07T06:28:16Z",
                expected_format: "2106-02-07T06:28:16+00:00",
            },
            DisplayTestCase {
                name: "sub-second is kept by Display and truncated by format",
                input: Time::millis(1_707_238_427_962),
                expected: "2024-02-06T16:53:47.962Z",
                expected_format: "2024-02-06T16:53:47+00:00",
            },
            DisplayTestCase {
                name: "last whole second in range",
                input: Time::millis(253_402_207_200_000),
                expected: "9999-12-30T22:00:00Z",
                expected_format: "9999-12-30T22:00:00+00:00",
            },
            DisplayTestCase {
                name: "first sub-second past the last whole second in range",
                input: Time::millis(253_402_207_200_001),
                expected: "9999-12-30T22:00:00.001Z",
                expected_format: "9999-12-30T22:00:00+00:00",
            },
            DisplayTestCase {
                name: "last millisecond in range",
                input: Time::millis(LAST_FINITE_MILLIS),
                expected: "9999-12-30T22:00:00.999Z",
                expected_format: "9999-12-30T22:00:00+00:00",
            },
            DisplayTestCase {
                name: "first millisecond past the range",
                input: Time::millis(LAST_FINITE_MILLIS + 1),
                expected: "∞",
                expected_format: "∞",
            },
            DisplayTestCase {
                name: "very large",
                input: Time::seconds(i64::from(i32::MAX) * 3500),
                expected: "∞",
                expected_format: "∞",
            },
            DisplayTestCase {
                name: "MAX",
                input: Time::MAX,
                expected: "∞",
                expected_format: "∞",
            },
            DisplayTestCase {
                name: "i16::MIN",
                input: Time::seconds(i64::from(i16::MIN)),
                expected: "1969-12-31T14:53:52Z",
                expected_format: "1969-12-31T14:53:52+00:00",
            },
            DisplayTestCase {
                name: "first millisecond in range",
                input: Time::millis(FIRST_FINITE_MILLIS),
                expected: "-009999-01-02T01:59:59Z",
                expected_format: "-9999-01-02T01:59:59+00:00",
            },
            DisplayTestCase {
                name: "last millisecond before the range",
                input: Time::millis(FIRST_FINITE_MILLIS - 1),
                expected: "-∞",
                expected_format: "-∞",
            },
            DisplayTestCase {
                name: "i64::MIN",
                input: Time::millis(i64::MIN),
                expected: "-∞",
                expected_format: "-∞",
            },
        ]
    }

    #[test]
    fn test_display() {
        for test in display_test_cases() {
            assert_eq!(
                test.expected,
                test.input.to_rfc3339(),
                "to_rfc3339 failed for test '{}'",
                test.name
            );
            assert_eq!(
                test.expected,
                test.input.to_string(),
                "Display failed for test '{}'",
                test.name
            );
            assert_eq!(
                test.expected_format,
                test.input.format("%Y-%m-%dT%H:%M:%S+00:00").to_string(),
                "format failed for test '{}'",
                test.name
            );
        }
    }

    #[test]
    fn test_time_window_display() {
        assert_eq!(
            "[1970-01-01T00:00:00Z, ∞]",
            TimeWindow::new(Time::EPOCH, Time::MAX).to_string()
        );
        assert_eq!(
            "[1970-01-01T01:00:00Z, 2024-02-06T16:53:47.962Z]",
            TimeWindow::new(Time::hours(1), Time::millis(1_707_238_427_962)).to_string()
        );
    }

    #[test]
    fn test_time_from_timestamp() {
        struct TestCase {
            name: &'static str,
            input: Timestamp,
            expected: Time,
        }

        let tests = vec![
            TestCase {
                name: "UNIX_EPOCH",
                input: Timestamp::UNIX_EPOCH,
                expected: Time::EPOCH,
            },
            TestCase {
                name: "MAX",
                input: Timestamp::MAX,
                expected: Time::millis(LAST_FINITE_MILLIS),
            },
            TestCase {
                name: "MIN",
                input: Timestamp::MIN,
                expected: Time::millis(FIRST_FINITE_MILLIS),
            },
        ];

        for test in tests {
            let actual = Time::from(test.input);
            assert_eq!(
                test.expected, actual,
                "From<Timestamp> failed for test '{}'",
                test.name
            );
            assert_eq!(
                test.input.strftime("%Y-%m-%dT%H:%M:%S").to_string(),
                actual.format("%Y-%m-%dT%H:%M:%S").to_string(),
                "converting back failed for test '{}'",
                test.name
            );
        }
    }

    #[test]
    fn test_duration_try_from_signed_duration() {
        assert_eq!(
            Ok(Duration::seconds(7) + Duration::millis(123)),
            Duration::try_from(SignedDuration::new(7, 123_999_999))
        );
        assert_eq!(
            Ok(Duration::seconds(-7) - Duration::millis(123)),
            Duration::try_from(SignedDuration::new(-7, -123_999_999))
        );
        assert!(Duration::try_from(SignedDuration::MAX).is_err());
        assert!(Duration::try_from(SignedDuration::MIN).is_err());
    }

    #[test]
    fn test_parse_from_rfc3339() {
        struct TestCase {
            name: &'static str,
            input: &'static str,
            expected: Time,
        }

        let tests = vec![
            TestCase {
                name: "EPOCH Z",
                input: "1970-01-01T00:00:00Z",
                expected: Time::EPOCH,
            },
            TestCase {
                name: "EPOCH UTC offset",
                input: "1970-01-01T00:00:00+00:00",
                expected: Time::EPOCH,
            },
            TestCase {
                name: "positive offset",
                input: "1970-01-01T01:00:00+01:00",
                expected: Time::EPOCH,
            },
            TestCase {
                name: "negative offset",
                input: "1969-12-31T23:00:00-01:00",
                expected: Time::EPOCH,
            },
            TestCase {
                name: "sub-millisecond truncation",
                input: "1970-01-01T02:51:07.123999Z",
                expected: Time::hours(2)
                    + Duration::minutes(51)
                    + Duration::seconds(7)
                    + Duration::millis(123),
            },
            TestCase {
                name: "sub-millisecond truncation towards zero before the epoch",
                input: "1969-12-31T23:59:59.999999Z",
                expected: Time::EPOCH,
            },
        ];

        for test in tests {
            assert_eq!(
                Ok(test.expected),
                Time::parse_from_rfc3339(test.input).map_err(|error| error.to_string()),
                "parse_from_rfc3339 failed for test '{}'",
                test.name
            );
        }
    }
}
