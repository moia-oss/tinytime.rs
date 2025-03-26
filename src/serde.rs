use core::fmt;
use std::str::FromStr;

use serde::Deserializer;
use serde::de::Error;
use serde::de::Visitor;

use crate::Duration;
use crate::Time;

#[cfg(feature = "chrono")]
impl Time {
    /// Helper method for deserializing an RFC 3339 string with `serde`.
    ///
    /// # Examples
    /// ```
    /// use tinytime::Duration;
    /// use tinytime::Time;
    ///
    /// #[derive(serde::Deserialize)]
    /// struct MyStruct {
    ///     #[serde(deserialize_with = "Time::deserialize_rfc3339")]
    ///     my_time: Time,
    /// }
    ///
    /// let json = r#"{ "my_time": "1970-01-01T02:51:00Z" }"#;
    /// let decoded: MyStruct = serde_json::from_str(json).unwrap();
    /// assert_eq!(
    ///     Time::EPOCH + Duration::hours(2) + Duration::minutes(51),
    ///     decoded.my_time
    /// );
    /// ```
    pub fn deserialize_rfc3339<'de, D>(value: D) -> Result<Time, D::Error>
    where
        D: Deserializer<'de>,
    {
        value.deserialize_str(TimeVisitor)
    }
}

#[cfg(feature = "chrono")]
struct TimeVisitor;

#[cfg(feature = "chrono")]
impl Visitor<'_> for TimeVisitor {
    type Value = Time;

    fn expecting(&self, formatter: &mut fmt::Formatter) -> std::fmt::Result {
        formatter.write_str("an RFC 3339 string")
    }

    fn visit_str<E>(self, v: &str) -> Result<Self::Value, E>
    where
        E: Error,
    {
        Time::parse_from_rfc3339(v).map_err(|e| E::custom(e.to_string()))
    }
}

impl Duration {
    /// Helper method for deserializing a duration string with `serde`.
    ///
    /// # Examples
    /// ```
    /// use tinytime::Duration;
    ///
    /// #[derive(serde::Deserialize)]
    /// struct MyStruct {
    ///     #[serde(deserialize_with = "Duration::deserialize_str")]
    ///     my_duration: Duration,
    /// }
    ///
    /// let json = r#"{ "my_duration": "1h20s" }"#;
    /// let decoded: MyStruct = serde_json::from_str(json).unwrap();
    /// assert_eq!(
    ///     Duration::hours(1) + Duration::seconds(20),
    ///     decoded.my_duration
    /// );
    /// ```
    pub fn deserialize_str<'de, D>(value: D) -> Result<Duration, D::Error>
    where
        D: Deserializer<'de>,
    {
        value.deserialize_str(DurationVisitor)
    }
}

struct DurationVisitor;

impl Visitor<'_> for DurationVisitor {
    type Value = Duration;

    fn expecting(&self, formatter: &mut fmt::Formatter) -> std::fmt::Result {
        formatter.write_str("a duration string")
    }

    fn visit_str<E>(self, v: &str) -> Result<Self::Value, E>
    where
        E: Error,
    {
        Duration::from_str(v).map_err(|e| E::custom(e.to_string()))
    }
}

#[cfg(test)]
mod test {
    use bincode::config;

    use crate::Duration;
    use crate::Time;
    use crate::TimeWindow;

    #[test]
    fn serde_json_time() {
        for expected in [Time::hours(7), Time::EPOCH, Time::MAX] {
            let encoded = serde_json::to_string(&expected).unwrap();
            let actual = serde_json::from_str(&encoded).unwrap();
            assert_eq!(expected, actual);
        }
    }

    #[test]
    fn serde_json_duration() {
        for expected in [
            Duration::millis(77777),
            Duration::MAX,
            Duration::ZERO,
            -Duration::MAX,
        ] {
            let encoded = serde_json::to_string(&expected).unwrap();
            let actual: Duration = serde_json::from_str(&encoded).unwrap();
            assert_eq!(expected, actual);
        }
    }

    #[test]
    fn serde_json_time_window() {
        for expected in [
            TimeWindow::new(Time::hours(7), Time::hours(19)),
            TimeWindow::widest(),
        ] {
            let encoded = serde_json::to_string(&expected).unwrap();
            let actual: TimeWindow = serde_json::from_str(&encoded).unwrap();
            assert_eq!(expected, actual);
        }
    }

    // Why unit tests for bincode?
    // In the past, we had a minor issue with how we supported serde:
    // We were only supporting self-describing formats (such as JSON) and didn't
    // support non-self-describing formats (such as bincode).
    // Upon finding this,
    // we removed the support to deserialize from different formats from within the
    // deserializer, but kept the possibility to add custom
    // (de)serialization.
    // Types from this crate can still be (de)serialized with serde
    // by using `serialize_with` as illustrated above in this file,
    // for self-describing and non-self-describing formats.
    // The following unit tests ensure that this option keeps working.
    #[test]
    fn serde_bincode_time() {
        for expected in [Time::hours(7), Time::EPOCH, Time::MAX] {
            let encoded = bincode::serde::encode_to_vec(expected, config::standard()).unwrap();
            let actual = bincode::serde::decode_from_slice(&encoded, config::standard())
                .unwrap()
                .0;
            assert_eq!(expected, actual);
        }
    }

    #[test]
    fn serde_bincode_duration() {
        for expected in [
            Duration::millis(77777),
            Duration::MAX,
            Duration::ZERO,
            -Duration::MAX,
        ] {
            let encoded = bincode::serde::encode_to_vec(expected, config::standard()).unwrap();
            let actual: Duration = bincode::serde::decode_from_slice(&encoded, config::standard())
                .unwrap()
                .0;
            assert_eq!(expected, actual);
        }
    }

    #[test]
    fn serde_bincode_time_window() {
        for expected in [
            TimeWindow::new(Time::hours(7), Time::hours(19)),
            TimeWindow::widest(),
        ] {
            let encoded = bincode::serde::encode_to_vec(expected, config::standard()).unwrap();
            let actual: TimeWindow =
                bincode::serde::decode_from_slice(&encoded, config::standard())
                    .unwrap()
                    .0;
            assert_eq!(expected, actual);
        }
    }
}
