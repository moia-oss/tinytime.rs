use std::fmt::Formatter;
use std::str::FromStr;

use serde::de::Visitor;
use serde::Deserialize;

use crate::Duration;
use crate::Time;

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

    fn expecting(&self, formatter: &mut Formatter) -> std::fmt::Result {
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
        i64::try_from(v)
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

/// Allows deserializing from strings, unsigned integers, and signed integers.
impl<'de> Deserialize<'de> for Duration {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        deserializer.deserialize_any(DurationVisitor)
    }
}

struct DurationVisitor;

impl<'de> Visitor<'de> for DurationVisitor {
    type Value = Duration;

    fn expecting(&self, formatter: &mut Formatter) -> std::fmt::Result {
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
        i64::try_from(v)
            .map_err(|e| E::custom(e.to_string()))
            .map(Duration::millis)
    }

    fn visit_i64<E>(self, v: i64) -> Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        Ok(Duration::millis(v))
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

#[cfg(test)]
mod test {
    use serde_test::assert_de_tokens;
    use serde_test::Token;

    use super::*;

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
