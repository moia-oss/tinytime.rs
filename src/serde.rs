use core::fmt;
use std::str::FromStr;

use serde::de::Error;
use serde::de::Visitor;
use serde::Deserializer;

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
