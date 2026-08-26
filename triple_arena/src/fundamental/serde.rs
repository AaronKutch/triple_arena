use serde::{Deserialize, Deserializer, Serialize, Serializer, ser::SerializeTuple};

use crate::{Link, LinkNoGen, traits::Ptr};

impl<P: Ptr, T: Serialize> Serialize for Link<P, T> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut s = serializer.serialize_tuple(3)?;
        s.serialize_element(&self.prev())?;
        s.serialize_element(&self.next())?;
        s.serialize_element(&self.t)?;
        s.end()
    }
}

impl<P: Ptr, T: Serialize> Serialize for LinkNoGen<P, T> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut s = serializer.serialize_tuple(3)?;
        s.serialize_element(&self.prev())?;
        s.serialize_element(&self.next())?;
        s.serialize_element(&self.t)?;
        s.end()
    }
}

impl<'de, P: Ptr, T> Deserialize<'de> for Link<P, T>
where
    T: Deserialize<'de>,
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let (prev, next, t): (Option<P>, Option<P>, T) = Deserialize::deserialize(deserializer)?;
        Ok(Link::new((prev, next), t))
    }
}

impl<'de, P: Ptr, T> Deserialize<'de> for LinkNoGen<P, T>
where
    T: Deserialize<'de>,
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let (prev, next, t): (Option<P::Inx>, Option<P::Inx>, T) =
            Deserialize::deserialize(deserializer)?;
        Ok(LinkNoGen::new((prev, next), t))
    }
}
