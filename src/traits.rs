pub trait Integer:
	Default
	+ num_traits::PrimInt
	+ num_traits::CheckedNeg
	+ num_traits::CheckedShl
	+ num_traits::CheckedShr
	+ num_traits::SaturatingMul
	+ num_traits::WrappingAdd
	+ num_traits::WrappingSub
	+ num_traits::WrappingMul
	+ num_traits::WrappingNeg
	+ num_traits::WrappingShl
	+ num_traits::WrappingShr
{
	const BITS: u32;
	const MIN: Self;
	const MAX: Self;

	type SignedSibling: Integer;
	type UnsignedSibling: Integer;


	// Ops not in num_traits
	fn checked_div_euclid(self, rhs: Self) -> Option<Self>;
	fn checked_rem_euclid(self, rhs: Self) -> Option<Self>;
	fn leading_ones(self) -> u32;
	fn trailing_ones(self) -> u32;
	fn reverse_bits(self) -> Self;
	fn saturating_div(self, rhs: Self) -> Self;
	fn saturating_pow(self, exp: u32) -> Self;
}


impl Integer for u8 {
	const BITS: u32 = u8::BITS;
	const MIN: Self = u8::MIN;
	const MAX: Self = u8::MAX;
	type SignedSibling = i8;
	type UnsignedSibling = Self;

	#[inline] fn checked_div_euclid(self, rhs: Self) -> Option<Self> { Self::checked_div_euclid(self, rhs) }
	#[inline] fn checked_rem_euclid(self, rhs: Self) -> Option<Self> { Self::checked_div_euclid(self, rhs) }
	#[inline] fn leading_ones(self) -> u32 { Self::leading_ones(self) }
	#[inline] fn trailing_ones(self) -> u32 { Self::trailing_ones(self) }
	#[inline] fn reverse_bits(self) -> Self { Self::reverse_bits(self) }
	#[inline] fn saturating_div(self, rhs: Self) -> Self { Self::saturating_div(self, rhs) }
	#[inline] fn saturating_pow(self, exp: u32) -> Self { Self::saturating_pow(self, exp) }
}


impl Integer for u16 {
	const BITS: u32 = u16::BITS;
	const MIN: Self = u16::MIN;
	const MAX: Self = u16::MAX;
	type SignedSibling = i16;
	type UnsignedSibling = Self;

	#[inline] fn checked_div_euclid(self, rhs: Self) -> Option<Self> { Self::checked_div_euclid(self, rhs) }
	#[inline] fn checked_rem_euclid(self, rhs: Self) -> Option<Self> { Self::checked_div_euclid(self, rhs) }
	#[inline] fn leading_ones(self) -> u32 { Self::leading_ones(self) }
	#[inline] fn trailing_ones(self) -> u32 { Self::trailing_ones(self) }
	#[inline] fn reverse_bits(self) -> Self { Self::reverse_bits(self) }
	#[inline] fn saturating_div(self, rhs: Self) -> Self { Self::saturating_div(self, rhs) }
	#[inline] fn saturating_pow(self, exp: u32) -> Self { Self::saturating_pow(self, exp) }
}


impl Integer for u32 {
	const BITS: u32 = u32::BITS;
	const MIN: Self = u32::MIN;
	const MAX: Self = u32::MAX;
	type SignedSibling = i32;
	type UnsignedSibling = Self;

	#[inline] fn checked_div_euclid(self, rhs: Self) -> Option<Self> { Self::checked_div_euclid(self, rhs) }
	#[inline] fn checked_rem_euclid(self, rhs: Self) -> Option<Self> { Self::checked_div_euclid(self, rhs) }
	#[inline] fn leading_ones(self) -> u32 { Self::leading_ones(self) }
	#[inline] fn trailing_ones(self) -> u32 { Self::trailing_ones(self) }
	#[inline] fn reverse_bits(self) -> Self { Self::reverse_bits(self) }
	#[inline] fn saturating_div(self, rhs: Self) -> Self { Self::saturating_div(self, rhs) }
	#[inline] fn saturating_pow(self, exp: u32) -> Self { Self::saturating_pow(self, exp) }
}


impl Integer for u64 {
	const BITS: u32 = u64::BITS;
	const MIN: Self = u64::MIN;
	const MAX: Self = u64::MAX;
	type SignedSibling = i64;
	type UnsignedSibling = Self;

	#[inline] fn checked_div_euclid(self, rhs: Self) -> Option<Self> { Self::checked_div_euclid(self, rhs) }
	#[inline] fn checked_rem_euclid(self, rhs: Self) -> Option<Self> { Self::checked_div_euclid(self, rhs) }
	#[inline] fn leading_ones(self) -> u32 { Self::leading_ones(self) }
	#[inline] fn trailing_ones(self) -> u32 { Self::trailing_ones(self) }
	#[inline] fn reverse_bits(self) -> Self { Self::reverse_bits(self) }
	#[inline] fn saturating_div(self, rhs: Self) -> Self { Self::saturating_div(self, rhs) }
	#[inline] fn saturating_pow(self, exp: u32) -> Self { Self::saturating_pow(self, exp) }
}


impl Integer for u128 {
	const BITS: u32 = u128::BITS;
	const MIN: Self = u128::MIN;
	const MAX: Self = u128::MAX;
	type SignedSibling = i128;
	type UnsignedSibling = Self;

	#[inline] fn checked_div_euclid(self, rhs: Self) -> Option<Self> { Self::checked_div_euclid(self, rhs) }
	#[inline] fn checked_rem_euclid(self, rhs: Self) -> Option<Self> { Self::checked_div_euclid(self, rhs) }
	#[inline] fn leading_ones(self) -> u32 { Self::leading_ones(self) }
	#[inline] fn trailing_ones(self) -> u32 { Self::trailing_ones(self) }
	#[inline] fn reverse_bits(self) -> Self { Self::reverse_bits(self) }
	#[inline] fn saturating_div(self, rhs: Self) -> Self { Self::saturating_div(self, rhs) }
	#[inline] fn saturating_pow(self, exp: u32) -> Self { Self::saturating_pow(self, exp) }
}


impl Integer for usize {
	const BITS: u32 = usize::BITS;
	const MIN: Self = usize::MIN;
	const MAX: Self = usize::MAX;
	type SignedSibling = isize;
	type UnsignedSibling = Self;

	#[inline] fn checked_div_euclid(self, rhs: Self) -> Option<Self> { Self::checked_div_euclid(self, rhs) }
	#[inline] fn checked_rem_euclid(self, rhs: Self) -> Option<Self> { Self::checked_div_euclid(self, rhs) }
	#[inline] fn leading_ones(self) -> u32 { Self::leading_ones(self) }
	#[inline] fn trailing_ones(self) -> u32 { Self::trailing_ones(self) }
	#[inline] fn reverse_bits(self) -> Self { Self::reverse_bits(self) }
	#[inline] fn saturating_div(self, rhs: Self) -> Self { Self::saturating_div(self, rhs) }
	#[inline] fn saturating_pow(self, exp: u32) -> Self { Self::saturating_pow(self, exp) }
}


impl Integer for i8 {
	const BITS: u32 = i8::BITS;
	const MIN: Self = i8::MIN;
	const MAX: Self = i8::MAX;
	type SignedSibling = Self;
	type UnsignedSibling = u8;

	#[inline] fn checked_div_euclid(self, rhs: Self) -> Option<Self> { Self::checked_div_euclid(self, rhs) }
	#[inline] fn checked_rem_euclid(self, rhs: Self) -> Option<Self> { Self::checked_div_euclid(self, rhs) }
	#[inline] fn leading_ones(self) -> u32 { Self::leading_ones(self) }
	#[inline] fn trailing_ones(self) -> u32 { Self::trailing_ones(self) }
	#[inline] fn reverse_bits(self) -> Self { Self::reverse_bits(self) }
	#[inline] fn saturating_div(self, rhs: Self) -> Self { Self::saturating_div(self, rhs) }
	#[inline] fn saturating_pow(self, exp: u32) -> Self { Self::saturating_pow(self, exp) }
}


impl Integer for i16 {
	const BITS: u32 = i16::BITS;
	const MIN: Self = i16::MIN;
	const MAX: Self = i16::MAX;
	type SignedSibling = Self;
	type UnsignedSibling = u16;

	#[inline] fn checked_div_euclid(self, rhs: Self) -> Option<Self> { Self::checked_div_euclid(self, rhs) }
	#[inline] fn checked_rem_euclid(self, rhs: Self) -> Option<Self> { Self::checked_div_euclid(self, rhs) }
	#[inline] fn leading_ones(self) -> u32 { Self::leading_ones(self) }
	#[inline] fn trailing_ones(self) -> u32 { Self::trailing_ones(self) }
	#[inline] fn reverse_bits(self) -> Self { Self::reverse_bits(self) }
	#[inline] fn saturating_div(self, rhs: Self) -> Self { Self::saturating_div(self, rhs) }
	#[inline] fn saturating_pow(self, exp: u32) -> Self { Self::saturating_pow(self, exp) }
}


impl Integer for i32 {
	const BITS: u32 = i32::BITS;
	const MIN: Self = i32::MIN;
	const MAX: Self = i32::MAX;
	type SignedSibling = Self;
	type UnsignedSibling = u32;

	#[inline] fn checked_div_euclid(self, rhs: Self) -> Option<Self> { Self::checked_div_euclid(self, rhs) }
	#[inline] fn checked_rem_euclid(self, rhs: Self) -> Option<Self> { Self::checked_div_euclid(self, rhs) }
	#[inline] fn leading_ones(self) -> u32 { Self::leading_ones(self) }
	#[inline] fn trailing_ones(self) -> u32 { Self::trailing_ones(self) }
	#[inline] fn reverse_bits(self) -> Self { Self::reverse_bits(self) }
	#[inline] fn saturating_div(self, rhs: Self) -> Self { Self::saturating_div(self, rhs) }
	#[inline] fn saturating_pow(self, exp: u32) -> Self { Self::saturating_pow(self, exp) }
}


impl Integer for i64 {
	const BITS: u32 = i64::BITS;
	const MIN: Self = i64::MIN;
	const MAX: Self = i64::MAX;
	type SignedSibling = Self;
	type UnsignedSibling = u64;

	#[inline] fn checked_div_euclid(self, rhs: Self) -> Option<Self> { Self::checked_div_euclid(self, rhs) }
	#[inline] fn checked_rem_euclid(self, rhs: Self) -> Option<Self> { Self::checked_div_euclid(self, rhs) }
	#[inline] fn leading_ones(self) -> u32 { Self::leading_ones(self) }
	#[inline] fn trailing_ones(self) -> u32 { Self::trailing_ones(self) }
	#[inline] fn reverse_bits(self) -> Self { Self::reverse_bits(self) }
	#[inline] fn saturating_div(self, rhs: Self) -> Self { Self::saturating_div(self, rhs) }
	#[inline] fn saturating_pow(self, exp: u32) -> Self { Self::saturating_pow(self, exp) }
}


impl Integer for i128 {
	const BITS: u32 = i128::BITS;
	const MIN: Self = i128::MIN;
	const MAX: Self = i128::MAX;
	type SignedSibling = Self;
	type UnsignedSibling = u128;

	#[inline] fn checked_div_euclid(self, rhs: Self) -> Option<Self> { Self::checked_div_euclid(self, rhs) }
	#[inline] fn checked_rem_euclid(self, rhs: Self) -> Option<Self> { Self::checked_div_euclid(self, rhs) }
	#[inline] fn leading_ones(self) -> u32 { Self::leading_ones(self) }
	#[inline] fn trailing_ones(self) -> u32 { Self::trailing_ones(self) }
	#[inline] fn reverse_bits(self) -> Self { Self::reverse_bits(self) }
	#[inline] fn saturating_div(self, rhs: Self) -> Self { Self::saturating_div(self, rhs) }
	#[inline] fn saturating_pow(self, exp: u32) -> Self { Self::saturating_pow(self, exp) }
}


impl Integer for isize {
	const BITS: u32 = isize::BITS;
	const MIN: Self = isize::MIN;
	const MAX: Self = isize::MAX;
	type SignedSibling = Self;
	type UnsignedSibling = usize;

	#[inline] fn checked_div_euclid(self, rhs: Self) -> Option<Self> { Self::checked_div_euclid(self, rhs) }
	#[inline] fn checked_rem_euclid(self, rhs: Self) -> Option<Self> { Self::checked_div_euclid(self, rhs) }
	#[inline] fn leading_ones(self) -> u32 { Self::leading_ones(self) }
	#[inline] fn trailing_ones(self) -> u32 { Self::trailing_ones(self) }
	#[inline] fn reverse_bits(self) -> Self { Self::reverse_bits(self) }
	#[inline] fn saturating_div(self, rhs: Self) -> Self { Self::saturating_div(self, rhs) }
	#[inline] fn saturating_pow(self, exp: u32) -> Self { Self::saturating_pow(self, exp) }
}
