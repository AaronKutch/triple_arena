#![cfg(feature = "serde_support")]

use std::num::{NonZeroU32, NonZeroU128};

use stacked_errors::{StackedError, ensure, ensure_eq};
use testcrate::{P0, P3};
use triple_arena::{
    Link,
    traits::*,
    utils::{LinkNoGen, PtrNoGen},
};

#[test]
fn serde() -> Result<(), StackedError> {
    let p0 = P0::_from_raw(
        NonZeroU32::new(7).unwrap(),
        NonZeroU128::new(u128::MAX - 7).unwrap(),
    );
    let v = postcard::to_allocvec(&p0).unwrap();
    ensure_eq!(v, vec![
        7, 248, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
        255, 3
    ]);
    ensure_eq!(postcard::from_bytes::<P0>(&v).unwrap(), p0);
    ensure_eq!(
        postcard::from_bytes::<P0>(&[7]),
        Err(postcard::Error::DeserializeUnexpectedEnd)
    );
    let s = ron::to_string(&p0).unwrap();
    ensure_eq!(s, "(7,340282366920938463463374607431768211448)");
    ensure_eq!(ron::from_str::<P0>(&s).unwrap(), p0);
    ensure!(ron::from_str::<P0>("7").is_err());

    // generationless
    let p3 = P3::_from_raw(NonZeroU32::new(7).unwrap(), ());
    let v = postcard::to_allocvec(&p3).unwrap();
    ensure_eq!(v, vec![7]);
    ensure_eq!(postcard::from_bytes::<P3>(&v).unwrap(), p3);
    ensure_eq!(
        postcard::take_from_bytes::<P3>(&[7, 3]),
        Ok((p3, [3].as_slice()))
    );
    let s = ron::to_string(&p3).unwrap();
    ensure_eq!(s, "7");
    ensure_eq!(ron::from_str::<P3>(&s).unwrap(), p3);
    ensure!(ron::from_str::<P3>("(7,3)").is_err());

    let p0 = PtrNoGen::<P0>::_from_raw(NonZeroU32::new(7).unwrap(), ());
    let v = postcard::to_allocvec(&p0).unwrap();
    ensure_eq!(v, vec![7]);
    ensure_eq!(postcard::from_bytes::<PtrNoGen<P0>>(&v).unwrap(), p0);
    let s = ron::to_string(&p0).unwrap();
    ensure_eq!(s, "7");
    ensure_eq!(ron::from_str::<PtrNoGen<P0>>(&s).unwrap(), p0);

    let p0 = P0::_from_raw(NonZeroU32::new(7).unwrap(), NonZeroU128::new(42).unwrap());
    let p1 = P0::_from_raw(NonZeroU32::new(6).unwrap(), NonZeroU128::new(7).unwrap());
    let link: Link<P0, String> = Link::new((Some(p0), Some(p1)), "67".to_owned());
    let v = postcard::to_allocvec(&link).unwrap();
    ensure_eq!(v, vec![1, 7, 42, 1, 6, 7, 2, 54, 55]);
    ensure_eq!(postcard::from_bytes::<Link<P0, String>>(&v).unwrap(), link);
    ensure_eq!(
        ron::to_string(&link).unwrap(),
        "(Some((7,42)),Some((6,7)),\"67\")"
    );
    let link: Link<P0, String> = Link::new((None, None), "67".to_owned());
    let v = postcard::to_allocvec(&link).unwrap();
    ensure_eq!(v, vec![0, 0, 2, 54, 55]);
    ensure_eq!(postcard::from_bytes::<Link<P0, String>>(&v).unwrap(), link);
    ensure_eq!(ron::to_string(&link).unwrap(), "(None,None,\"67\")");

    let p0 = P0::_from_raw(NonZeroU32::new(7).unwrap(), NonZeroU128::new(42).unwrap());
    let p1 = P0::_from_raw(NonZeroU32::new(6).unwrap(), NonZeroU128::new(7).unwrap());
    let link: LinkNoGen<P0, String> =
        LinkNoGen::new((Some(p0.inx()), Some(p1.inx())), "67".to_owned());
    let v = postcard::to_allocvec(&link).unwrap();
    ensure_eq!(v, vec![1, 7, 1, 6, 2, 54, 55]);
    ensure_eq!(
        postcard::from_bytes::<LinkNoGen<P0, String>>(&v).unwrap(),
        link
    );
    ensure_eq!(ron::to_string(&link).unwrap(), "(Some(7),Some(6),\"67\")");
    let link: LinkNoGen<P0, String> = LinkNoGen::new((None, None), "67".to_owned());
    let v = postcard::to_allocvec(&link).unwrap();
    ensure_eq!(v, vec![0, 0, 2, 54, 55]);
    ensure_eq!(
        postcard::from_bytes::<LinkNoGen<P0, String>>(&v).unwrap(),
        link
    );
    ensure_eq!(ron::to_string(&link).unwrap(), "(None,None,\"67\")");

    Ok(())
}
