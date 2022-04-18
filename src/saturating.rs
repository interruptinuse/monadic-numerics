use crate::traits::Integer;


#[derive(Clone, Copy, Debug)]
#[repr(transparent)]
pub struct Saturating<T>(T) where T: Integer;


impl<T> Saturating<T> where T: Integer {
	pub const BITS: u32 = <T as Integer>::BITS;

	pub const BYTES: usize = <T as Integer>::BITS as usize / 8;

	pub const MIN: Self = Self(<T as Integer>::MIN);

	pub const MAX: Self = Self(<T as Integer>::MAX);

	#[inline]
	pub const fn new(inner: T) -> Self {
		Self(inner)
	}
}


#[test]
fn auto_traits() {
	use static_assertions::assert_impl_all;

	assert_impl_all!(Saturating<u8>: Send, Sync);
	assert_impl_all!(Saturating<u16>: Send, Sync);
	assert_impl_all!(Saturating<u32>: Send, Sync);
	assert_impl_all!(Saturating<u64>: Send, Sync);
	assert_impl_all!(Saturating<u128>: Send, Sync);
	assert_impl_all!(Saturating<usize>: Send, Sync);

	assert_impl_all!(Saturating<i8>: Send, Sync);
	assert_impl_all!(Saturating<i16>: Send, Sync);
	assert_impl_all!(Saturating<i32>: Send, Sync);
	assert_impl_all!(Saturating<i64>: Send, Sync);
	assert_impl_all!(Saturating<i128>: Send, Sync);
	assert_impl_all!(Saturating<isize>: Send, Sync);

}


#[test]
#[cfg(feature = "std")]
fn auto_panic_traits() {
	use std::panic::{UnwindSafe, RefUnwindSafe};
	use static_assertions::assert_impl_all;

	assert_impl_all!(Saturating<u8>: UnwindSafe, RefUnwindSafe);
	assert_impl_all!(Saturating<u16>: UnwindSafe, RefUnwindSafe);
	assert_impl_all!(Saturating<u32>: UnwindSafe, RefUnwindSafe);
	assert_impl_all!(Saturating<u64>: UnwindSafe, RefUnwindSafe);
	assert_impl_all!(Saturating<u128>: UnwindSafe, RefUnwindSafe);
	assert_impl_all!(Saturating<usize>: UnwindSafe, RefUnwindSafe);

	assert_impl_all!(Saturating<i8>: UnwindSafe, RefUnwindSafe);
	assert_impl_all!(Saturating<i16>: UnwindSafe, RefUnwindSafe);
	assert_impl_all!(Saturating<i32>: UnwindSafe, RefUnwindSafe);
	assert_impl_all!(Saturating<i64>: UnwindSafe, RefUnwindSafe);
	assert_impl_all!(Saturating<i128>: UnwindSafe, RefUnwindSafe);
	assert_impl_all!(Saturating<isize>: UnwindSafe, RefUnwindSafe);
}
