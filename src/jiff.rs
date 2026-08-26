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
    pub fn format<'a>(&self, fmt: &'a str) -> strtime::Display<'a> {
        if let Ok(timestamp) = Timestamp::from_millisecond(self.0) {
            timestamp.strftime(fmt)
        } else {
            let infinity = if self.0.is_positive() { "∞" } else { "-∞" };
            Timestamp::UNIX_EPOCH.strftime(infinity)
        }
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
    /// 1996-12-19T16:39:57Z.
    ///
    /// Formatting is forwarded to the [`Display`] implementation of
    /// [`jiff::Timestamp`].
    ///
    /// Values outside jiff's timestamp range, such as `Time::MAX`, are
    /// formatted as "∞" or "-∞".
    ///
    /// # Example
    ///
    /// ```
    /// use tinytime::Time;
    /// assert_eq!(
    ///     "1996-12-19T16:39:57Z",
    ///     Time::seconds(851_013_597).to_rfc3339()
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
        match Timestamp::from_millisecond(self.0) {
            Ok(timestamp) => Display::fmt(&timestamp, f),
            Err(_) => f.write_str(if self.0.is_positive() { "∞" } else { "-∞" }),
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

    use crate::Duration;
    use crate::Time;
    use crate::TimeWindow;

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
                expected: "1970-01-01T00:00:00Z".to_string(),
            },
            TestCase {
                name: "i16::MAX + 1",
                input: Time::seconds(i64::from(i16::MAX) + 1),
                expected: "1970-01-01T09:06:08Z".to_string(),
            },
            TestCase {
                name: "i32::MAX + 1",
                input: Time::seconds(i64::from(i32::MAX) + 1),
                expected: "2038-01-19T03:14:08Z".to_string(),
            },
            TestCase {
                name: "u32::MAX + 1",
                input: Time::seconds(i64::from(u32::MAX) + 1),
                expected: "2106-02-07T06:28:16Z".to_string(),
            },
            TestCase {
                name: "sub-second",
                input: Time::millis(1_707_238_427_962),
                expected: "2024-02-06T16:53:47.962Z".to_string(),
            },
            TestCase {
                name: "very large",
                input: Time::seconds(i64::from(i32::MAX) * 3500),
                expected: "∞".to_string(),
            },
            TestCase {
                name: "MAX",
                input: Time::MAX,
                expected: "∞".to_string(),
            },
            TestCase {
                name: "i16::MIN",
                input: Time::seconds(i64::from(i16::MIN)),
                expected: "1969-12-31T14:53:52Z".to_string(),
            },
            TestCase {
                name: "i64::MIN",
                input: Time::millis(i64::MIN),
                expected: "-∞".to_string(),
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
                test.input.to_string(),
                "Display failed for test '{}'",
                test.name
            );
        }
    }

    #[test]
    fn test_format() {
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
                name: "sub-second is truncated",
                input: Time::millis(1_707_238_427_962),
                expected: "2024-02-06T16:53:47+00:00".to_string(),
            },
            TestCase {
                name: "MAX",
                input: Time::MAX,
                expected: "∞".to_string(),
            },
            TestCase {
                name: "i64::MIN",
                input: Time::millis(i64::MIN),
                expected: "-∞".to_string(),
            },
        ];
        for test in tests {
            assert_eq!(
                test.expected,
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
    fn test_duration_from_signed_duration() {
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
