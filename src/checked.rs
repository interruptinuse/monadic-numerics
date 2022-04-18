use core::ops::Deref;
use core::ops::DerefMut;

use crate::traits::Integer;


/// Provides safe, checked arithmetics on `T` with propagating error.  This type
/// is implemented internally as `Option<T>`.
///
/// # Example
/// ```
/// # use monadic_numerics::prelude::*;
/// # fn main() -> anyhow::Result<()> {
/// let mut c: Checked::<u8> = Checked::MIN;
/// assert_eq!(*c, Some(u8::MIN));
/// assert_eq!(*(c / 0), None);
/// assert_eq!(*(c - 1), None);
/// c -= 1;
/// assert_eq!(*c, None);
///
/// // The error propagates
/// c += 20;
/// assert_eq!(*c, None);
/// # Ok(()) }
/// ```
#[derive(Clone, Copy, Debug)]
#[repr(transparent)]
pub struct Checked<T>(Option<T>) where T: Integer;


impl<T> Checked<T> where T: Integer {
	/// The size of the underlying integer type `T` in bits.
	///
	/// ```
	/// # use monadic_numerics::prelude::*;
	/// assert_eq!(Checked::<usize>::BITS, usize::BITS);
	/// ```
	/// ---
	/// For the corresponding standard API, see e.g.
	/// [`usize::BITS`][core::primitive::usize::BITS].
	pub const BITS: u32 = <T as Integer>::BITS;


	/// The size of the underlying integer type `T` in bytes.
	///
	/// ```
	/// # use monadic_numerics::prelude::*;
	/// assert_eq!(Checked::<usize>::BYTES, std::mem::size_of::<usize>());
	/// ```
	pub const BYTES: usize = <T as Integer>::BITS as usize / 8;


	/// The smallest value that can be represented by the underlying integer
	/// type `T`.
	///
	/// ```
	/// # use monadic_numerics::prelude::*;
	/// assert_eq!(*Checked::<i16>::MIN, Some(-32768i16));
	/// ```
	/// ---
	/// For the corresponding standard API, see e.g.
	/// [`i16::MIN`][core::primitive::i16::MIN].
	pub const MIN: Self = Self(Some(<T as Integer>::MIN));


	/// The largest value that can be represented by the underlying integer
	/// type `T`.
	///
	/// ```
	/// # use monadic_numerics::prelude::*;
	/// assert_eq!(*Checked::<i16>::MAX, Some(32767i16));
	/// ```
	/// ---
	/// For the corresponding standard API, see e.g.
	/// [`i16::MAX`][core::primitive::i16::MAX].
	pub const MAX: Self = Self(Some(<T as Integer>::MAX));


	/// The value representing a propagating error, such as overflow, underflow,
	/// division by zero, etc.
	///
	/// You should not compare to this constant to detect errors, because it is
	/// not equal to itself, just like a NaN:
	///
	/// ```
	/// # use monadic_numerics::prelude::*;
	/// assert_ne!(Checked::<u8>::ERROR, Checked::<u8>::ERROR);
	/// ```
	///
	/// [`Checked::is_error()`] should be used instead, or, since [`Checked`]
	/// implements
	/// [`Deref`][std::ops::Deref]`<Target=`[`Option`][std::option::Option]`<T>>`,
	/// through [`Option::is_none()`].
	pub const ERROR: Self = Self(None);


	/// Creates a new non-error instance of `Self` from the underlying numeric
	/// value.
	///
	/// # Example
	/// ```
	/// # use monadic_numerics::prelude::*;
	/// assert_eq!(*Checked::<i16>::new(i16::MIN), Some(i16::MIN));
	/// ```
	#[inline]
	pub const fn new(inner: T) -> Self {
		Self(Some(inner))
	}


	/// Returns `true` if `Self` contains an error.
	/// ```
	/// # use monadic_numerics::prelude::*;
	/// assert!((Checked::<u8>::new(1) / 0).is_error());
	/// ```
	#[inline]
	pub const fn is_error(&self) -> bool {
		self.inner_ref().is_none()
	}


	/// Consumes `self` and returns the inner [`Option<T>`].
	///
	/// ```
	/// # use monadic_numerics::prelude::*;
	/// assert_eq!(Checked::<u8>::new(10).into_inner(), Some(10));
	/// assert_eq!(Checked::<u8>::ERROR.into_inner(), None);
	/// ```
	#[inline]
	pub const fn into_inner(self) -> Option<T> {
		self.0
	}


	/// Creates a new instance of `Checked<T>` from `U: TryInto<T>`, mapping
	/// the error to `Checked::ERROR`.
	///
	/// This inherent method is needed because of Rust's blanket [`TryInto`]
	/// impls, and will become obsolete in case specialization lands.
	///
	/// ```
	/// # use monadic_numerics::prelude::*;
	/// assert_eq!(*Checked::<u8>::try_from(255u32), Some(255u8));
	/// assert_eq!(*Checked::<u8>::try_from(256u32), None);
	/// ```
	#[inline]
	pub fn try_from<U: Integer + TryInto<T>>(inner: U) -> Self {
		inner
			.try_into()
			.map(Checked::new)
			.unwrap_or(Checked::ERROR)
	}


	/// Map `Checked<T>` to `Checked<U>` by transforming the inner [`Option`].
	#[inline]
	pub fn visit<U: Integer, F: FnOnce(Option<T>) -> Option<U>>(self, visitor: F) -> Checked<U> {
		Checked::<U>(visitor(self.0))
	}


	#[inline]
	const fn inner_ref(&self) -> &Option<T> {
		&self.0
	}


	#[inline]
	fn inner_mut(&mut self) -> &mut Option<T> {
		&mut self.0
	}
}


/// [`Option`]-like `self` method impls.
impl<T> Checked<T> where T: Integer {
	/// Returns the contained numeric value, consuming `self`.
	///
	/// # Panics
	/// - If `self.is_error()` with a panic message provided by `msg`.
	///
	/// # Example
	/// This works:
	/// ```
	/// # use monadic_numerics::prelude::*;
	/// assert_eq!(Checked::<u8>::new(0).expect("Checked::new is always valid"), 0);
	/// ```
	///
	/// This panics:
	/// ```should_panic
	/// # use monadic_numerics::prelude::*;
	/// (Checked::<u8>::new(1) / 0).expect("Division by zero results in error");
	/// ```
	/// ---
	/// For the corresponding standard API, see
	/// [`Option::expect`][core::option::Option::expect].
	#[inline]
	pub fn expect(self, msg: &str) -> T {
		self.into_inner().expect(msg)
	}


	/// Returns the contained numeric value, consuming `self`.
	///
	/// # Panics
	/// - If `self.is_error()`.
	///
	/// # Example
	/// This works:
	/// ```
	/// # use monadic_numerics::prelude::*;
	/// assert_eq!(Checked::<i8>::MAX.unwrap(), i8::MAX);
	/// ```
	/// Unwrapping a `Checked::ERROR` always panics:
	/// ```should_panic
	/// # use monadic_numerics::prelude::*;
	/// let _ = Checked::<i32>::ERROR.unwrap();
	/// ```
	/// ---
	/// For the corresponding standard API, see
	/// [`Option::unwrap`][core::option::Option::unwrap].
	#[inline]
	pub fn unwrap(self) -> T {
		self.into_inner().unwrap()
	}


	/// Returns the contained numeric value or, if `self.is_error()`, a provided
	/// default.
	///
	/// ```
	/// # use monadic_numerics::prelude::*;
	/// let mut c = Checked::<usize>::new(5);
	/// assert_eq!(c.unwrap_or(0), 5);
	/// c /= 0;
	/// assert_eq!(c.unwrap_or(0), 0);
	/// ```
	/// ---
	/// For the corresponding standard API, see
	/// [`Option::unwrap_or`][core::option::Option::unwrap_or].
	#[inline]
	pub fn unwrap_or(self, default: T) -> T {
		self.into_inner().unwrap_or(default)
	}


	/// Returns the contained numeric value or, if `self.is_error()`, computes
	/// it from a closure.
	///
	/// ```
	/// # use monadic_numerics::prelude::*;
	/// let k = 41;
	/// let closure = || k + 1;
	/// let c = Checked::<usize>::MAX;
	/// assert_eq!(c.unwrap_or_else(closure), usize::MAX);
	/// let c = c + 1;
	/// assert_eq!(c.unwrap_or_else(closure), 42);
	/// ```
	/// ---
	/// For the corresponding standard API, see
	/// [`Option::unwrap_or_else`][core::option::Option::unwrap_or_else].
	#[inline]
	pub fn unwrap_or_else<F: FnOnce() -> T>(self, f: F) -> T {
		self.into_inner().unwrap_or_else(f)
	}


	/// Returns the contained numeric value or, if `self.is_error()`,
	/// `<T as Default>::default()`.
	///
	/// ```
	/// # use monadic_numerics::prelude::*;
	/// let c = Checked::<usize>::new(42);
	/// assert_eq!(c.unwrap_or_default(), 42);
	/// assert_eq!((c / 0).unwrap_or_default(), 0);
	/// ```
	/// ---
	/// For the corresponding standard API, see
	/// [`Option::unwrap_or_default`][core::option::Option::unwrap_or_default].
	#[inline]
	pub fn unwrap_or_default(self) -> T {
		self.into_inner().unwrap_or_default()
	}


	/// Returns the contained numeric value without checking if
	/// `self.is_error()`.
	///
	/// # Safety
	/// Calling this method on a [`Checked::ERROR`] is undefined behavior.
	///
	/// ```
	/// # use monadic_numerics::prelude::*;
	/// let c: Checked<usize> = Some(42usize).into();
	/// assert_eq!(unsafe { c.unwrap_unchecked() }, 42);
	/// ```
	///
	/// ```no_run
	/// # use monadic_numerics::prelude::*;
	/// let c: Checked<usize> = Checked::ERROR;
	/// assert_eq!(unsafe { c.unwrap_unchecked() }, 0); // Undefined behavior
	/// ```
	/// ---
	/// For the corresponding standard API, see
	/// [`Option::unwrap_unchecked`][core::option::Option::unwrap_unchecked].
	#[inline]
	pub unsafe fn unwrap_unchecked(self) -> T {
		self.into_inner().unwrap_unchecked()
	}


	/// Maps a `Checked<T>` to `Checked<U>` by applying a function to the
	/// contained integer, if any.  `U` must be a primitive integer type.
	///
	/// ```
	/// # use monadic_numerics::prelude::*;
	/// let c = Checked::<u8>::new(42);
	/// assert_eq!(*c.map(|i| i.count_ones()), Some(3));
	/// ```
	///
	/// ```compile_fail
	/// # use monadic_numerics::prelude::*;
	/// let c = Checked::<u8>::new(42);
	/// // Checked<String> is not a valid type
	/// assert_eq!(*c.map(|i| format!("{}", i)), Some("42"));
	/// ```
	/// ---
	/// For the corresponding standard API, see
	/// [`Option::map`][core::option::Option::map].
	#[inline]
	pub fn map<U: Integer, F: FnOnce(T) -> U>(self, f: F) -> Checked<U> {
		self.visit(|o| o.map(f))
	}


	/// Calls the provided closure with a reference to the contained value (if
	/// any).
	///
	/// ```
	/// # use monadic_numerics::prelude::*;
	/// let inspect = |c: Checked<u8>| {
	///   let mut foo = "no value".to_string();
	///   c.inspect(|c| { foo = format!("{}", c); });
	///   foo
	/// };
	///
	/// assert_eq!("no value", inspect(Checked::<u8>::ERROR));
	/// assert_eq!("10", inspect(Checked::<u8>::new(10)));
	/// ```
	/// ---
	/// For the corresponding standard API, see
	/// [`Option::inspect`][core::option::Option::inspect].
	#[inline]
	pub fn inspect<F: FnOnce(&T)>(self, f: F) -> Self {
		self.visit(|o| o.map(|i| { f(&i); i }) )
	}


	/// Returns the provided default (if error), or applies a function to
	/// the contained value (if any).
	///
	/// ```
	/// # use monadic_numerics::prelude::*;
	/// assert_eq!(Checked::<usize>::new(0b11011).map_or(42, |i| i.count_ones()), 4);
	/// assert_eq!((Checked::<usize>::new(0b11011) / 0).map_or(42, |i| i.count_ones()), 42);
	/// ```
	/// ---
	/// For the corresponding standard API, see
	/// [`Option::map_or`][core::option::Option::map_or].
	#[inline]
	pub fn map_or<U: Integer, F: FnOnce(T) -> U>(self, default: U, f: F) -> Checked<U> {
		self.visit(|o| o.map_or(default, f).into())
	}


	/// Computes a default function (if error), or applies a different function
	/// to the contained value (if any).
	///
	/// ```
	/// # use monadic_numerics::prelude::*;
	/// let half: u32 = 21;
	/// assert_eq!(Checked::<usize>::new(0b11011).map_or_else(|| half * 2, |i| i.count_ones()), 4);
	/// assert_eq!((Checked::<usize>::new(0b11011) / 0).map_or_else(|| half * 2, |i| i.count_ones()), 42);
	/// ```
	/// ---
	/// For the corresponding standard API, see
	/// [`Option::map_or_else`][core::option::Option::map_or_else].
	#[inline]
	pub fn map_or_else<U: Integer, D: FnOnce() -> U, F: FnOnce(T) -> U>(self, default: D, f: F) -> Checked<U> {
		self.visit(|o| o.map_or_else(default, f).into())
	}


	/// Transforms the inner `Option<T>` into a [`Result<T, E>`], mapping
	/// [`Some(v)`][core::option::Option::Some] to
	/// [`Ok(v)`][core::result::Result::Ok] and [`None`] ([`Checked::ERROR`]) to
	/// [`Err(err)`][core::result::Result::Err].
	///
	/// ```
	/// # use monadic_numerics::prelude::*;
	/// assert_eq!(Checked::<u8>::new(4).ok_or(()), Ok(4));
	/// assert_eq!((Checked::<u8>::MAX + 1).ok_or(()), Err(()));
	/// ```
	/// ---
	/// For the corresponding standard API, see
	/// [`Option::ok_or`][core::option::Option::ok_or].
	#[inline]
	pub fn ok_or<E>(self, err: E) -> Result<T, E> {
		self.into_inner().ok_or(err)
	}


	/// Transforms the inner `Option<T>` into a [`Result<T, E>`], mapping
	/// [`Some(v)`][core::option::Option::Some] to
	/// [`Ok(v)`][core::result::Result::Ok] and [`None`] ([`Checked::ERROR`]) to
	/// [`Err(err)`][core::result::Result::Err].
	///
	/// ```
	/// # use monadic_numerics::prelude::*;
	/// assert_eq!(Checked::<u8>::new(4).ok_or_else(|| ()), Ok(4));
	/// assert_eq!((Checked::<u8>::MAX + 1).ok_or_else(|| ()), Err(()));
	/// ```
	/// ---
	/// For the corresponding standard API, see
	/// [`Option::ok_or_else`][core::option::Option::ok_or_else].
	#[inline]
	pub fn ok_or_else<E, F: FnOnce() -> E>(self, err: F) -> Result<T, E> {
		self.into_inner().ok_or_else(err)
	}


	/// Returns `Self::ERROR` if error, otherwise returns `optb`.
	///
	/// ```
	/// # use monadic_numerics::prelude::*;
	/// assert_eq!(*Checked::<u8>::ERROR.and(Checked::<u8>::from(2)), None);
	/// assert_eq!(*Checked::<u8>::from(1).and(Checked::<u8>::from(2)), Some(2));
	/// ```
	/// ---
	/// For the corresponding standard API, see
	/// [`Option::and`][core::option::Option::and].
	#[inline]
	pub fn and<U: Integer>(self, optb: Checked<U>) -> Checked<U> {
		optb.filter(|_| !self.is_none())
	}


	/// Returns `Self::ERROR` if error, otherwise calls `f` with `self` and
	/// returns the result.
	///
	/// For a possibly more ergonomic alternative, see
	/// [`Checked::and_then_checked`].
	///
	/// ```
	/// # use monadic_numerics::prelude::*;
	/// let mut counter: usize = 0;
	/// let mut plus_one = |c: Checked<usize>| c.and_then(|i| { counter += 1; i.checked_add(1) });
	/// let c = Checked::<usize>::MAX;
	/// assert_eq!(*plus_one(c-1), Some(usize::MAX));
	/// assert_eq!(*plus_one(c), None);
	/// assert_eq!(*plus_one(Checked::ERROR), None); // Error, plus_one isn't run
	/// assert_eq!(counter, 2);
	/// ```
	/// ---
	/// For the corresponding standard API, see
	/// [`Option::and_then`][core::option::Option::and_then].
	#[inline]
	pub fn and_then<U: Integer, F: FnOnce(T) -> Option<U>>(self, f: F) -> Checked<U> {
		self.visit(|o| o.and_then(f))
	}


	/// Returns `Checked::<U>::ERROR` if error, otherwise calls `f` with `self`
	/// and returns the result.
	///
	/// ```
	/// # use monadic_numerics::prelude::*;
	/// let mut counter: usize = 0;
	/// let mut plus_one = |c: Checked<usize>| c.and_then_checked(|i| { counter += 1; i + 1 });
	/// let c = Checked::<usize>::MAX;
	/// assert_eq!(*plus_one(c - 1), Some(usize::MAX));
	/// assert_eq!(*plus_one(c), None);
	/// assert_eq!(*plus_one(c / 0), None); // Error, plus_one isn't run
	/// assert_eq!(counter, 2);
	/// ```
	#[inline]
	pub fn and_then_checked<U: Integer, F: FnOnce(Checked<T>) -> Checked<U>>(self, f: F) -> Checked<U> {
		if !self.is_error() {
			f(self)
		}
		else {
			Checked::<U>::ERROR
		}
	}


	#[inline]
	pub fn filter<P: FnOnce(&T) -> bool>(self, predicate: P) -> Self {
		self.visit(|o| o.filter(predicate))
	}


	/// ```
	/// # use monadic_numerics::prelude::*;
	/// assert_eq!(*Checked::<u8>::from(1).or(Checked::<u8>::from(2)), Some(1));
	/// assert_eq!(*Checked::<u8>::ERROR.or(Checked::<u8>::from(2)), Some(2));
	/// ```
	#[inline]
	pub fn or(self, optb: Checked<T>) -> Checked<T> {
		if self.is_some() { self } else { optb }
	}


	#[inline]
	pub fn or_else<F: FnOnce() -> Checked<T>>(self, f: F) -> Self {
		if self.is_some() { self } else { f() }
	}


	#[inline]
	pub fn xor(self, other: Self) -> Self {
		match (*self, *other) {
			(Some(_), None) => self,
			(None, Some(_)) => other,
			_ => Self::ERROR,
		}
	}


	#[inline]
	pub fn zip_with<U: Integer, I: Integer, F: FnOnce(T, U) -> Option<I>>(self, c2: Checked<U>, f: F) -> Checked<I> {
		self.and_then(|i1| c2.and_then(|i2| f(i1, i2)).0)
	}


	#[inline]
	pub fn zip_with_inner<U: Integer, I, F: FnOnce(T, U) -> I>(self, c2: Checked<U>, f: F) -> Option<I> {
		match (self.into_inner(), c2.into_inner()) {
			(Some(i1), Some(i2)) => Some(f(i1, i2)),
			_ => None,
		}
	}


	#[inline]
	pub fn wrap_into_option(self) -> Option<Self> {
		self.into_inner().map(|i| Self::new(i))
	}
}


/// Signed integer methods.
impl<T: Integer + num_traits::Signed> Checked<T> {
	/// Computes the absolute value of `self`.
	///
	/// # Overflow behavior
	/// The absolute value of `T::MIN` overflows `T`. In debug mode,
	/// `Checked::<T>::new(T::MIN).abs()` will panic, optimized code will return
	/// `T::MIN`.  For a panic-safe version of this method, see
	/// [`Checked::checked_abs()`].
	///
	/// # Panics
	/// - `Checked::<T>::MIN.abs()` will panic in debug mode.
	#[inline]
	pub fn abs(&self) -> Self {
		self.map(|i| <T as num_traits::Signed>::abs(&i))
	}


	/// Computes the absolute value of `self`.
	///
	/// # Overflow behavior
	/// The absolute value of `T::MIN` overflows `T`.  As opposed to
	/// [`Checked::abs`], `Checked::<T>::new(T::MIN).checked_abs()` will
	/// return `Checked::ERROR`.
	#[inline]
	pub fn checked_abs(&self) -> Self {
		self.and_then(|i| if i == T::MIN { None } else { Some(<T as num_traits::Signed>::abs(&i)) })
	}


	//pub fn abs_diff<U: Into<Checked<T>>>(self, other: U) -> Checked<<T as Integer>::UnsignedSibling> {
		//self.zip_with(other.into(), |i1, i2| {
		//})
		//
	//}


	#[inline]
	pub fn signum(self) -> Self {
		self.map(|i| i.signum())
	}


	#[inline]
	pub fn is_positive(self) -> bool {
		matches!(*self, Some(i) if i.is_positive())
	}


	#[inline]
	pub fn is_negative(self) -> bool {
		matches!(*self, Some(i) if i.is_negative())
	}
}


/// Unsigned integer methods.
impl<T: Integer + num_traits::Unsigned> Checked<T> {
}


/// Common methods.
impl<T: Integer> Checked<T> {
	#[inline]
	pub fn checked_neg(self) -> Self {
		<Self as num_traits::CheckedNeg>::checked_neg(&self)
			.unwrap_or(Self::ERROR)
	}


	#[inline]
	pub fn checked_add(self, rhs: Self) -> Self {
		<Self as core::ops::Add>::add(self, rhs)
	}


	#[inline]
	pub fn checked_sub(self, rhs: Self) -> Self {
		<Self as core::ops::Sub>::sub(self, rhs)
	}


	#[inline]
	pub fn checked_mul(self, rhs: Self) -> Self {
		<Self as core::ops::Mul>::mul(self, rhs)
	}


	#[inline]
	pub fn checked_div(self, rhs: Self) -> Self {
		<Self as core::ops::Div>::div(self, rhs)
	}


	#[inline]
	pub fn checked_div_euclid(self, rhs: Self) -> Self {
		self.zip_with(rhs, |i1, i2| <T as Integer>::checked_div_euclid(i1, i2))
	}


	#[inline]
	pub fn checked_rem(self, rhs: Self) -> Self {
		<Self as core::ops::Rem>::rem(self, rhs)
	}


	#[inline]
	pub fn checked_rem_euclid(self, rhs: Self) -> Self {
		self.zip_with(rhs, |i1, i2| <T as Integer>::checked_rem_euclid(i1, i2))
	}


	#[inline]
	pub fn checked_pow(self, mut exp: u32) -> Self {
		let mut base = self;
		let mut acc: Self = <Self as num_traits::One>::one();

		if <Self as num_traits::One>::is_one(&self) {
			return self;
		};

		if exp == 0 {
			return acc;
		};

		while exp > 1 {
			if (exp & 1) == 1 {
				acc *= base;

				if acc.is_error() {
					return Self::ERROR;
				};
			};

			exp /= 2;

			base *= base;

			if base.is_error() {
				return Self::ERROR;
			};
		};

		acc * base
	}


	#[inline]
	pub fn checked_shl<U: Integer + TryInto<u32>>(self, rhs: U) -> Self {
		<Self as core::ops::Shl<U>>::shl(self, rhs)
	}


	#[inline]
	pub fn checked_shr<U: Integer + TryInto<u32>>(self, rhs: U) -> Self {
		<Self as core::ops::Shr<U>>::shr(self, rhs)
	}


	#[inline]
	pub fn saturating_add<U: Into<Checked<T>>>(self, rhs: U) -> Self {
		self.zip_with(rhs.into(), |i1, i2| Some(i1.saturating_add(i2)))
	}


	#[inline]
	pub fn saturating_sub<U: Into<Checked<T>>>(self, rhs: U) -> Self {
		self.zip_with(rhs.into(), |i1, i2| Some(i1.saturating_sub(i2)))
	}


	#[inline]
	pub fn saturating_mul<U: Into<Checked<T>>>(self, rhs: U) -> Self {
		let rhs = rhs.into();
		self.zip_with(rhs, |i1, i2| Some(i1.saturating_mul(&i2)))
	}


	#[inline]
	pub fn saturating_div<U: Into<Checked<T>>>(self, rhs: U) -> Self {
		let rhs = rhs.into();
		self
			.filter(|_| !<Checked<T> as num_traits::Zero>::is_zero(&rhs))
			.zip_with(rhs, |i1, i2| Some(i1.saturating_div(i2)))
	}

	#[inline]
	pub fn saturating_pow(self, exp: u32) -> Self {
		self.map(|i| i.saturating_pow(exp))
	}


	#[inline]
	pub fn wrapping_add<U: Into<Checked<T>>>(self, rhs: U) -> Self {
		self.zip_with(rhs.into(), |i1, i2| Some(<T as num_traits::WrappingAdd>::wrapping_add(&i1, &i2)))
	}


	#[inline]
	pub fn wrapping_sub<U: Into<Checked<T>>>(self, rhs: U) -> Self {
		self.zip_with(rhs.into(), |i1, i2| Some(<T as num_traits::WrappingSub>::wrapping_sub(&i1, &i2)))
	}


	#[inline]
	pub fn wrapping_mul<U: Into<Checked<T>>>(self, rhs: U) -> Self {
		self.zip_with(rhs.into(), |i1, i2| Some(<T as num_traits::WrappingMul>::wrapping_mul(&i1, &i2)))
	}


	#[inline]
	pub fn wrapping_neg(self) -> Self {
		self.map(|i| <T as num_traits::WrappingNeg>::wrapping_neg(&i))
	}


	#[inline]
	pub fn wrapping_shl<U: Into<Checked<u32>>>(self, rhs: U) -> Self {
		self.zip_with(rhs.into(), |i1, i2| Some(<T as num_traits::WrappingShl>::wrapping_shl(&i1, i2)))
	}


	#[inline]
	pub fn wrapping_shr<U: Into<Checked<u32>>>(self, rhs: U) -> Self {
		self.zip_with(rhs.into(), |i1, i2| Some(<T as num_traits::WrappingShr>::wrapping_shr(&i1, i2)))
	}

	// [TODO] wrapping_div_euclid
	// [TODO] wrapping_rem_euclid
	// [TODO] wrapping_abs
	// [TODO] wrapping_pow
	// [TODO] are overflowing methods needed?



	#[inline]
	pub fn count_zeros(self) -> Checked<u32> {
		self.map(|i| i.count_zeros())
	}


	#[inline]
	pub fn count_ones(self) -> Checked<u32> {
		self.map(|i| i.count_ones())
	}


	#[inline]
	pub fn leading_zeros(self) -> Checked<u32> {
		self.map(|i| i.leading_zeros())
	}


	#[inline]
	pub fn leading_ones(self) -> Checked<u32> {
		self.map(|i| <T as Integer>::leading_ones(i))
	}


	#[inline]
	pub fn trailing_zeros(self) -> Checked<u32> {
		self.map(|i| i.trailing_zeros())
	}


	#[inline]
	pub fn trailing_ones(self) -> Checked<u32> {
		self.map(|i| <T as Integer>::trailing_ones(i))
	}


	#[inline]
	pub fn rotate_left(self, n: u32) -> Self {
		self.map(|i| i.rotate_left(n))
	}


	#[inline]
	pub fn rotate_right(self, n: u32) -> Self {
		self.map(|i| i.rotate_right(n))
	}


	#[inline]
	pub fn swap_bytes(self) -> Self {
		self.map(|i| i.swap_bytes())
	}


	#[inline]
	pub fn reverse_bits(self) -> Self {
		self.map(|i| <T as Integer>::reverse_bits(i))
	}


	#[inline]
	pub fn from_be(x: T) -> Self {
		Self::new(T::from_be(x))
	}


	#[inline]
	pub fn from_le(x: T) -> Self {
		Self::new(T::from_le(x))
	}


	#[inline]
	pub fn to_be(self) -> Self {
		self.map(|i| i.to_be())
	}


	#[inline]
	pub fn to_le(self) -> Self {
		self.map(|i| i.to_le())
	}
}


#[test]
fn checked_pow() {
	for i in 1u32..10 {
		for j in 1u8..=u8::MAX {
			assert_eq!(j.checked_pow(i), *Checked::<u8>::new(j).checked_pow(i));
		};

		for j in i8::MIN..=i8::MAX {
			assert_eq!(j.checked_pow(i), *Checked::<i8>::new(j).checked_pow(i));
		};
	};
}


#[test]
fn assert_traits() {
	use core::fmt::{Debug, Display};
	use core::marker::Unpin;
	use static_assertions::assert_impl_all;

	assert_impl_all!(Checked<u8>: Debug, Display, Send, Sync, Unpin);
	assert_impl_all!(Checked<u16>: Debug, Display, Send, Sync, Unpin);
	assert_impl_all!(Checked<u32>: Debug, Display, Send, Sync, Unpin);
	assert_impl_all!(Checked<u64>: Debug, Display, Send, Sync, Unpin);
	assert_impl_all!(Checked<u128>: Debug, Display, Send, Sync, Unpin);
	assert_impl_all!(Checked<usize>: Debug, Display, Send, Sync, Unpin);

	assert_impl_all!(Checked<i8>: Debug, Display, Send, Sync, Unpin);
	assert_impl_all!(Checked<i16>: Debug, Display, Send, Sync, Unpin);
	assert_impl_all!(Checked<i32>: Debug, Display, Send, Sync, Unpin);
	assert_impl_all!(Checked<i64>: Debug, Display, Send, Sync, Unpin);
	assert_impl_all!(Checked<i128>: Debug, Display, Send, Sync, Unpin);
	assert_impl_all!(Checked<isize>: Debug, Display, Send, Sync, Unpin);
}


#[test]
#[cfg(feature = "std")]
fn assert_std_traits() {
	use std::panic::{UnwindSafe, RefUnwindSafe};
	use static_assertions::assert_impl_all;

	assert_impl_all!(Checked<u8>: UnwindSafe, RefUnwindSafe);
	assert_impl_all!(Checked<u16>: UnwindSafe, RefUnwindSafe);
	assert_impl_all!(Checked<u32>: UnwindSafe, RefUnwindSafe);
	assert_impl_all!(Checked<u64>: UnwindSafe, RefUnwindSafe);
	assert_impl_all!(Checked<u128>: UnwindSafe, RefUnwindSafe);
	assert_impl_all!(Checked<usize>: UnwindSafe, RefUnwindSafe);

	assert_impl_all!(Checked<i8>: UnwindSafe, RefUnwindSafe);
	assert_impl_all!(Checked<i16>: UnwindSafe, RefUnwindSafe);
	assert_impl_all!(Checked<i32>: UnwindSafe, RefUnwindSafe);
	assert_impl_all!(Checked<i64>: UnwindSafe, RefUnwindSafe);
	assert_impl_all!(Checked<i128>: UnwindSafe, RefUnwindSafe);
	assert_impl_all!(Checked<isize>: UnwindSafe, RefUnwindSafe);
}


impl<T: Integer> Default for Checked<T> {
	fn default() -> Self {
		Self::from(<T as Default>::default())
	}
}


impl<T: Integer> Deref for Checked<T> {
	type Target = Option<T>;

	fn deref(&self) -> &Self::Target {
		self.inner_ref()
	}
}


impl<T: Integer> DerefMut for Checked<T> {
	fn deref_mut(&mut self) -> &mut Self::Target {
		self.inner_mut()
	}
}


impl<T: Integer> PartialEq<T> for Checked<T> {
	fn eq(&self, other: &T) -> bool {
		matches!(self.deref(), Some(i) if i == other)
	}
}


impl<T: Integer> PartialEq<Checked<T>> for Checked<T> {
	fn eq(&self, other: &Checked<T>) -> bool {
		matches!((self.deref(), other.deref()), (Some(i1), Some(i2)) if i1 == i2)
	}
}


impl<T: Integer> PartialEq<Option<T>> for Checked<T> {
	fn eq(&self, other: &Option<T>) -> bool {
		matches!((self.deref(), other), (Some(i1), Some(i2)) if i1 == i2)
	}
}


#[test]
fn partial_eq() {
	assert_eq!(Checked::<i32>::from(42)+10, Checked::<i32>::from(45)+7);
	// Two overflowed values are not equal to one another
	assert_ne!(Checked::<u8>::ERROR, Checked::<u8>::ERROR);
	assert_ne!(Checked::<u8>::from(u8::MAX)+1, Checked::<u8>::from(u8::MAX)+1);
}


impl<T: Integer> PartialOrd<T> for Checked<T> {
	fn partial_cmp(&self, other: &T) -> Option<core::cmp::Ordering> {
		self
			.as_ref()
			.and_then(|i| <T as PartialOrd<T>>::partial_cmp(i, other))
	}
}


impl<T: Integer> PartialOrd<Checked<T>> for Checked<T> {
	fn partial_cmp(&self, other: &Checked<T>) -> Option<core::cmp::Ordering> {
		match (**self, **other) {
			(Some(i1), Some(i2)) => <T as core::cmp::PartialOrd>::partial_cmp(&i1, &i2),
			_ => None,
		}
	}
}


impl<T: Integer, U: Integer + Into<T>> From<U> for Checked<T> {
	fn from(input: U) -> Self {
		Self(Some(input.into()))
	}
}


impl<T: Integer, U: Integer + Into<T>> From<Option<U>> for Checked<T> {
	fn from(o: Option<U>) -> Self {
		Self(o.map(|i| i.into()))
	}
}


impl<T: Integer, U: Integer + Into<T>> From<Option<Checked<U>>> for Checked<T> {
	fn from(o: Option<Checked<U>>) -> Self {
		o.unwrap_or(Checked::<U>::ERROR).map(|i| i.into())
	}
}


impl<T: Integer + core::str::FromStr> core::str::FromStr for Checked<T> {
	type Err = core::convert::Infallible;

	/// Parses `Checked<T>` from `input`, returning `Checked::<T>::ERROR` if
	/// failed to parse a value.
	fn from_str(input: &str) -> Result<Self, Self::Err> {
		let result = <T as core::str::FromStr>
			::from_str(input)
			.map(|i| Self::from(i))
			.unwrap_or(Self::ERROR);
		Ok(result)
	}
}


impl<T: Integer> core::fmt::Display for Checked<T> {
	fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
		match self.deref() {
			Some(i) => write!(f, "{}", i),
			None => write!(f, "<Error>"),
		}
	}
}


impl<T: Integer> num_traits::identities::Zero for Checked<T> {
	fn zero() -> Self {
		Self::from(<T as num_traits::Zero>::zero())
	}

	fn is_zero(&self) -> bool {
		*self == <T as num_traits::Zero>::zero()
	}
}


impl<T: Integer> num_traits::identities::One for Checked<T> {
	fn one() -> Self {
		Self::from(<T as num_traits::One>::one())
	}

	fn is_one(&self) -> bool {
		*self == <T as num_traits::One>::one()
	}
}


impl<T: Integer + core::ops::Neg<Output=T>> core::ops::Neg for Checked<T> {
	type Output = Self;

	fn neg(self) -> Self::Output {
		self.and_then(|i| Some(<T as core::ops::Neg>::neg(i)))
	}
}


impl<T: Integer + num_traits::Num> num_traits::Num for Checked<T> {
	type FromStrRadixErr = <T as num_traits::Num>::FromStrRadixErr;

	fn from_str_radix(s: &str, r: u32) -> Result<Self, Self::FromStrRadixErr> {
		<T as num_traits::Num>
			::from_str_radix(s, r)
			.map(|t| Self::from(t))
	}
}


impl<T: Integer + num_traits::Unsigned> num_traits::Unsigned for Checked<T> { }


impl<T: Integer + num_traits::Signed> num_traits::Signed for Checked<T> {
	fn abs(&self) -> Self {
		self.and_then(|i| Some(<T as num_traits::Signed>::abs(&i)))
	}

	fn abs_sub(&self, rhs: &Checked<T>) -> Self {
		self.zip_with(*rhs, |i1, i2| Some(<T as num_traits::Signed>::abs_sub(&i1, &i2)))
	}

	fn signum(&self) -> Self {
		self.and_then(|i| Some(<T as num_traits::Signed>::signum(&i)))
	}

	fn is_positive(&self) -> bool {
		matches!(self.deref(), Some(i) if <T as num_traits::Signed>::is_positive(i))
	}

	fn is_negative(&self) -> bool {
		matches!(self.deref(), Some(i) if <T as num_traits::Signed>::is_negative(i))
	}
}


#[test]
fn signed_unsigned() {
	use static_assertions::assert_impl_all;
	use static_assertions::assert_not_impl_any;

	assert_impl_all!(Checked<u8>: num_traits::Unsigned);
	assert_impl_all!(Checked<u16>: num_traits::Unsigned);
	assert_impl_all!(Checked<u32>: num_traits::Unsigned);
	assert_impl_all!(Checked<u64>: num_traits::Unsigned);
	assert_impl_all!(Checked<u128>: num_traits::Unsigned);
	assert_impl_all!(Checked<usize>: num_traits::Unsigned);
	assert_not_impl_any!(Checked<u8>: num_traits::Signed);
	assert_not_impl_any!(Checked<u16>: num_traits::Signed);
	assert_not_impl_any!(Checked<u32>: num_traits::Signed);
	assert_not_impl_any!(Checked<u64>: num_traits::Signed);
	assert_not_impl_any!(Checked<u128>: num_traits::Signed);
	assert_not_impl_any!(Checked<usize>: num_traits::Signed);

	assert_impl_all!(Checked<i8>: num_traits::Signed);
	assert_impl_all!(Checked<i16>: num_traits::Signed);
	assert_impl_all!(Checked<i32>: num_traits::Signed);
	assert_impl_all!(Checked<i64>: num_traits::Signed);
	assert_impl_all!(Checked<i128>: num_traits::Signed);
	assert_impl_all!(Checked<isize>: num_traits::Signed);
	assert_not_impl_any!(Checked<i8>: num_traits::Unsigned);
	assert_not_impl_any!(Checked<i16>: num_traits::Unsigned);
	assert_not_impl_any!(Checked<i32>: num_traits::Unsigned);
	assert_not_impl_any!(Checked<i64>: num_traits::Unsigned);
	assert_not_impl_any!(Checked<i128>: num_traits::Unsigned);
	assert_not_impl_any!(Checked<isize>: num_traits::Unsigned);
}


impl<T: Integer + num_traits::AsPrimitive<U>, U: 'static + Integer> num_traits::AsPrimitive<Checked<U>> for Checked<T> {
	fn as_(self) -> Checked<U> {
		self.map(|i| i.as_())
	}
}


impl<T: Integer> core::iter::Sum<T> for Checked<T> {
	fn sum<I: Iterator<Item=T>>(iter: I) -> Self {
		iter.fold(<Checked::<T> as num_traits::Zero>::zero(), |a, b| a + b)
	}
}


impl<'a, T: Integer> core::iter::Sum<&'a T> for Checked<T> {
	fn sum<I: Iterator<Item=&'a T>>(iter: I) -> Self {
		iter.fold(<Checked::<T> as num_traits::Zero>::zero(), |a, b| a + *b)
	}
}


impl<T: Integer, U: Integer + Into<T>> core::iter::Sum<Checked<U>> for Checked<T> {
	fn sum<I: Iterator<Item=Checked<U>>>(iter: I) -> Self {
		iter.fold(<Checked::<T> as num_traits::Zero>::zero(), |a, b| a + b.map(|i| i.into()))
	}
}


#[test]
fn sum_iter() {
	let mut data = vec![85u8, 85u8, 85u8];
	assert_eq!(*<Checked::<u8> as core::iter::Sum<&u8>>::sum(data.iter()), Some(255));
	data.push(1);
	assert_eq!(*<Checked::<u8> as core::iter::Sum<&u8>>::sum(data.iter()), None);
	data.push(10);
	assert_eq!(*<Checked::<u8> as core::iter::Sum<&u8>>::sum(data.iter()), None);
}


impl<T: Integer> core::iter::Product<T> for Checked<T> {
	fn product<I: Iterator<Item=T>>(iter: I) -> Self {
		iter.fold(<Checked::<T> as num_traits::One>::one(), |a, b| a * b)
	}
}


impl<'a, T: Integer> core::iter::Product<&'a T> for Checked<T> {
	fn product<I: Iterator<Item=&'a T>>(iter: I) -> Self {
		iter.fold(<Checked::<T> as num_traits::One>::one(), |a, b| a * *b)
	}
}


impl<T: Integer> core::iter::Product<Checked<T>> for Checked<T> {
	fn product<I: Iterator<Item=Checked<T>>>(iter: I) -> Self {
		iter.fold(<Checked::<T> as num_traits::One>::one(), |a, b| a * b)
	}
}


#[test]
fn product_iter() {
}


#[cfg(feature = "try_trait")]
impl<T: Integer> core::ops::FromResidual for Checked<T> {
	fn from_residual(_: Option<core::convert::Infallible>) -> Self {
		Self::ERROR
	}
}


#[cfg(feature = "try_trait")]
impl<T: Integer> core::ops::Try for Checked<T> {
	type Output = T;
	type Residual = Option<core::convert::Infallible>;

	fn from_output(o: Self::Output) -> Self {
		Self::new(o)
	}

	fn branch(self) -> core::ops::ControlFlow<Self::Residual, Self::Output> {
		match self.into_inner() {
			Some(i) => core::ops::ControlFlow::Continue(i),
			None => core::ops::ControlFlow::Break(None),
		}
	}
}


impl<T: Integer> core::ops::Add<T> for Checked<T> {
	type Output = Self;

	#[inline]
	fn add(self, rhs: T) -> Self::Output {
		self.and_then(|i| i.checked_add(&rhs))
	}
}


impl<T: Integer> core::ops::Add<Checked<T>> for Checked<T> {
	type Output = Self;

	#[inline]
	fn add(self, rhs: Checked<T>) -> Self::Output {
		self.zip_with(rhs, |i1, i2| i1.checked_add(&i2))
	}
}


impl<T: Integer> core::ops::AddAssign<T> for Checked<T> {
	#[inline]
	fn add_assign(&mut self, rhs: T) {
		*self = <Checked<T> as core::ops::Add<T>>::add(*self, rhs);
	}
}


impl<T: Integer> core::ops::AddAssign<Checked<T>> for Checked<T> {
	#[inline]
	fn add_assign(&mut self, rhs: Checked<T>) {
		*self = <Checked<T> as core::ops::Add<Checked<T>>>::add(*self, rhs);
	}
}


#[test]
fn add() {
	let mut c: Checked<i8> = Checked::from(i8::MAX - 1);
	assert_eq!(c, 126);
	assert_eq!(*c, Some(126));
	c += 1;
	assert_eq!(c, 127);
	assert_eq!(*c, Some(127));
	c += 1;
	assert!(c.is_none());
	// Propagating overflow
	c += -1;
	assert_ne!(c, 127);
	assert!(c.is_none());

	let mut c: Checked<i8> = Checked::from(i8::MAX / 2);
	assert_eq!(*c, Some(63));
	assert_eq!(*(c + c + Checked::<i8>::from(1)), Some(127));
	c = c + c + Checked::<i8>::from(2);
	assert!(c.is_none());
	c += 1;
	assert!(c.is_none());
	// Propagating overflow
	c += -2;
	assert_ne!(c, 127);
	assert!(c.is_none());

	let mut c: Checked<i8> = Checked::from(i8::MIN);
	assert_eq!(*c, Some(-128));
	c += -1;
	assert_ne!(c, i8::MIN);
	assert_ne!(c, 0);
	assert_ne!(c, i8::MAX);
	assert_eq!(*c, None);

	assert_eq!(*(Checked::<u8>::from(5) + Checked::<u8>::ERROR), None);
}



impl<T: Integer> core::ops::Sub<T> for Checked<T> {
	type Output = Self;

	#[inline]
	fn sub(self, rhs: T) -> Self::Output {
		self.and_then(|i| i.checked_sub(&rhs))
	}
}


impl<T: Integer> core::ops::Sub<Checked<T>> for Checked<T> {
	type Output = Self;

	#[inline]
	fn sub(self, rhs: Checked<T>) -> Self::Output {
		self.zip_with(rhs, |i1, i2| i1.checked_sub(&i2))
	}
}


impl<T: Integer> core::ops::SubAssign<T> for Checked<T> {
	#[inline]
	fn sub_assign(&mut self, rhs: T) {
		*self = <Checked<T> as core::ops::Sub<T>>::sub(*self, rhs);
	}
}


impl<T: Integer> core::ops::SubAssign<Checked<T>> for Checked<T> {
	#[inline]
	fn sub_assign(&mut self, rhs: Checked<T>) {
		*self = <Checked<T> as core::ops::Sub<Checked<T>>>::sub(*self, rhs);
	}
}


#[test]
fn sub() {
	let mut c: Checked<i8> = Checked::from(i8::MIN);
	assert_eq!(c, -128);
	c -= 1;
	assert!(c.is_none());
	// propagating underflow
	c += 1;
	assert_ne!(c, -128);
	assert!(c.is_none());

	let mut c: Checked<i8> = Checked::from(i8::MIN / 2);
	assert_eq!(c, -64);
	c = c + c + 1;
	assert_eq!(c, -127);
	c -= 2;
	assert!(c.is_none());
	// propagating underflow
	c += 1;
	assert_ne!(c, -128);
	assert!(c.is_none());
}


impl<T: Integer> core::ops::Mul<T> for Checked<T> {
	type Output = Self;

	#[inline]
	fn mul(self, rhs: T) -> Self::Output {
		self.and_then(|i| i.checked_mul(&rhs))
	}
}


impl<T: Integer> core::ops::Mul<Checked<T>> for Checked<T> {
	type Output = Self;

	#[inline]
	fn mul(self, rhs: Checked<T>) -> Self::Output {
		self.zip_with(rhs, |i1, i2| i1.checked_mul(&i2))
	}
}


impl<T: Integer> core::ops::MulAssign<T> for Checked<T> {
	#[inline]
	fn mul_assign(&mut self, rhs: T) {
		*self = <Checked<T> as core::ops::Mul<T>>::mul(*self, rhs);
	}
}


impl<T: Integer> core::ops::MulAssign<Checked<T>> for Checked<T> {
	#[inline]
	fn mul_assign(&mut self, rhs: Checked<T>) {
		*self = <Checked<T> as core::ops::Mul<Checked<T>>>::mul(*self, rhs);
	}
}


#[test]
fn mul() {
	let mut c: Checked<i8> = Checked::from(i8::MIN / 2);
	assert_eq!(c, -64);
	c *= 2;
	assert_eq!(c, -128);
	assert_eq!(*(c + (c / 64 / 2)), None);
}


impl<T: Integer> core::ops::Div<T> for Checked<T> {
	type Output = Self;

	#[inline]
	fn div(self, rhs: T) -> Self::Output {
		self.and_then(|i| i.checked_div(&rhs))
	}
}


impl<T: Integer> core::ops::Div<Checked<T>> for Checked<T> {
	type Output = Self;

	#[inline]
	fn div(self, rhs: Checked<T>) -> Self::Output {
		self.zip_with(rhs, |i1, i2| i1.checked_div(&i2))
	}
}


impl<T: Integer> core::ops::DivAssign<T> for Checked<T> {
	#[inline]
	fn div_assign(&mut self, rhs: T) {
		*self = <Checked<T> as core::ops::Div<T>>::div(*self, rhs);
	}
}


impl<T: Integer> core::ops::DivAssign<Checked<T>> for Checked<T> {
	#[inline]
	fn div_assign(&mut self, rhs: Checked<T>) {
		*self = <Checked<T> as core::ops::Div<Checked<T>>>::div(*self, rhs);
	}
}


#[test]
fn div() {
	let mut c: Checked<u8> = Checked::from(u8::MAX);
	assert_eq!(c, 255);
	// propagating division by zero
	c /= 0;
	assert_ne!(c, 255);
	assert_ne!(c, 0);
	assert!(c.is_none());
	let d = c + 1;
	assert_ne!(d, 255);
	assert_ne!(d, 0);
	assert!(d.is_none());
	assert_ne!(d, c + 1);
}


impl<T: Integer> core::ops::Rem<T> for Checked<T> {
	type Output = Self;

	#[inline]
	fn rem(self, rhs: T) -> Self::Output {
		self
			.filter(|_| !<T as num_traits::Zero>::is_zero(&rhs))
			.and_then(|i| Some(i % rhs))
	}
}


impl<T: Integer> core::ops::Rem<Checked<T>> for Checked<T> {
	type Output = Self;

	#[inline]
	fn rem(self, rhs: Checked<T>) -> Self::Output {
		self
			.filter(|_| !<Checked<T> as num_traits::Zero>::is_zero(&rhs))
			.zip_with(rhs, |i1, i2| Some(i1 % i2))
	}
}


impl<T: Integer> core::ops::RemAssign<T> for Checked<T> {
	#[inline]
	fn rem_assign(&mut self, rhs: T) {
		*self = <Checked<T> as core::ops::Rem<T>>::rem(*self, rhs);
	}
}


impl<T: Integer> core::ops::RemAssign<Checked<T>> for Checked<T> {
	#[inline]
	fn rem_assign(&mut self, rhs: Checked<T>) {
		*self = <Checked<T> as core::ops::Rem<Checked<T>>>::rem(*self, rhs);
	}
}


#[test]
fn rem() {
	let mut c: Checked<u8> = Checked::from(128);
	assert_eq!(*c, Some(128));
	c %= 7;
	assert_eq!(*c, Some(2));
	c -= 2;
	assert_eq!(*c, Some(0));
	// propagating division by zero
	c %= c;
	assert_ne!(*c, Some(0));
	assert!(c.is_none());
	c += 1;
	assert_ne!(*c, Some(0));
	assert!(c.is_none());
	c /= 0;
	assert_ne!(*c, Some(0));
	assert!(c.is_none());
}


impl<T: Integer> core::ops::Not for Checked<T> {
	type Output = Self;

	#[inline]
	fn not(self) -> Self {
		self.and_then(|i| Some(<T as core::ops::Not>::not(i)))
	}
}


impl<T: Integer> core::ops::BitOr<T> for Checked<T> {
	type Output = Self;

	#[inline]
	fn bitor(self, rhs: T) -> Self::Output {
		self.and_then(|i| Some(<T as core::ops::BitOr<T>>::bitor(i, rhs)))
	}
}


impl<T: Integer> core::ops::BitOr<Checked<T>> for Checked<T> {
	type Output = Self;

	#[inline]
	fn bitor(self, rhs: Checked<T>) -> Self::Output {
		self.zip_with(rhs, |i1, i2| Some(<T as core::ops::BitOr<T>>::bitor(i1, i2)))
	}
}


impl<T: Integer> core::ops::BitOrAssign<T> for Checked<T> {
	#[inline]
	fn bitor_assign(&mut self, rhs: T) {
		*self = <Checked<T> as core::ops::BitOr<T>>::bitor(*self, rhs);
	}
}


impl<T: Integer> core::ops::BitOrAssign<Checked<T>> for Checked<T> {
	#[inline]
	fn bitor_assign(&mut self, rhs: Checked<T>) {
		*self = <Checked<T> as core::ops::BitOr<Checked<T>>>::bitor(*self, rhs);
	}
}


impl<T: Integer> core::ops::BitAnd<T> for Checked<T> {
	type Output = Self;

	#[inline]
	fn bitand(self, rhs: T) -> Self::Output {
		self.and_then(|i| Some(<T as core::ops::BitAnd<T>>::bitand(i, rhs)))
	}
}


impl<T: Integer> core::ops::BitAnd<Checked<T>> for Checked<T> {
	type Output = Self;

	#[inline]
	fn bitand(self, rhs: Checked<T>) -> Self::Output {
		self.zip_with(rhs, |i1, i2| Some(<T as core::ops::BitAnd<T>>::bitand(i1, i2)))
	}
}


impl<T: Integer> core::ops::BitAndAssign<T> for Checked<T> {
	#[inline]
	fn bitand_assign(&mut self, rhs: T) {
		*self = <Checked<T> as core::ops::BitAnd<T>>::bitand(*self, rhs);
	}
}


impl<T: Integer> core::ops::BitAndAssign<Checked<T>> for Checked<T> {
	#[inline]
	fn bitand_assign(&mut self, rhs: Checked<T>) {
		*self = <Checked<T> as core::ops::BitAnd<Checked<T>>>::bitand(*self, rhs);
	}
}


impl<T: Integer> core::ops::BitXor<T> for Checked<T> {
	type Output = Self;

	#[inline]
	fn bitxor(self, rhs: T) -> Self::Output {
		self.and_then(|i| Some(<T as core::ops::BitXor<T>>::bitxor(i, rhs)))
	}
}


impl<T: Integer> core::ops::BitXor<Checked<T>> for Checked<T> {
	type Output = Self;

	#[inline]
	fn bitxor(self, rhs: Checked<T>) -> Self::Output {
		self.zip_with(rhs, |i1, i2| Some(<T as core::ops::BitXor<T>>::bitxor(i1, i2)))
	}
}


impl<T: Integer> core::ops::BitXorAssign<T> for Checked<T> {
	#[inline]
	fn bitxor_assign(&mut self, rhs: T) {
		*self = <Checked<T> as core::ops::BitXor<T>>::bitxor(*self, rhs);
	}
}


impl<T: Integer> core::ops::BitXorAssign<Checked<T>> for Checked<T> {
	#[inline]
	fn bitxor_assign(&mut self, rhs: Checked<T>) {
		*self = <Checked<T> as core::ops::BitXor<Checked<T>>>::bitxor(*self, rhs);
	}
}


impl<T: Integer, Rhs: Integer + TryInto<u32>> core::ops::Shl<Rhs> for Checked<T> {
	type Output = Self;

	#[inline]
	fn shl(self, rhs: Rhs) -> Self::Output {
		let rhs = Checked::<u32>::from(<Rhs as TryInto<u32>>::try_into(rhs).ok());
		self.zip_with(rhs, |i1, i2| <T as num_traits::CheckedShl>::checked_shl(&i1, i2))
	}
}


impl<T: Integer, Rhs: Integer + TryInto<u32>> core::ops::Shl<Checked<Rhs>> for Checked<T> {
	type Output = Self;

	#[inline]
	fn shl(self, rhs: Checked<Rhs>) -> Self::Output {
		let rhs: Checked::<u32> = rhs.and_then(|i| i.try_into().ok());
		self.zip_with(rhs, |i1, i2| <T as num_traits::CheckedShl>::checked_shl(&i1, i2))
	}
}


impl<T: Integer, Rhs: Integer + TryInto<u32>> core::ops::ShlAssign<Rhs> for Checked<T> {
	#[inline]
	fn shl_assign(&mut self, rhs: Rhs) {
		*self = <Checked<T> as core::ops::Shl<Rhs>>::shl(*self, rhs);
	}
}


impl<T: Integer, Rhs: Integer + TryInto<u32>> core::ops::ShlAssign<Checked<Rhs>> for Checked<T> {
	#[inline]
	fn shl_assign(&mut self, rhs: Checked<Rhs>) {
		*self = <Checked<T> as core::ops::Shl<Checked<Rhs>>>::shl(*self, rhs);
	}
}


#[test]
fn shl() {
	let c = Checked::<u32>::new(42);
	let r = Checked::<i8>::new(4);
	assert_eq!(*(c << r), Some(0x02A0));
	assert_eq!(*(c << 26), Some(0xA8000000));
	assert_eq!(*(c << 30), Some(0x80000000));
	assert_eq!(*(c << 31), Some(0));
	assert_eq!(42u32.checked_shl(31), Some(0));
	assert_eq!(*(c << 32), None);
	assert_eq!(42u32.checked_shl(32), None);
	assert_eq!(*(c << Checked::<i32>::ERROR), None);
}


impl<T: Integer, Rhs: Integer + TryInto<u32>> core::ops::Shr<Rhs> for Checked<T> {
	type Output = Self;

	#[inline]
	fn shr(self, rhs: Rhs) -> Self::Output {
		let rhs = Checked::<u32>::from(<Rhs as TryInto<u32>>::try_into(rhs).ok());
		self.zip_with(rhs, |i1, i2| <T as num_traits::CheckedShr>::checked_shr(&i1, i2))
	}
}


impl<T: Integer, Rhs: Integer + TryInto<u32>> core::ops::Shr<Checked<Rhs>> for Checked<T> {
	type Output = Self;

	#[inline]
	fn shr(self, rhs: Checked<Rhs>) -> Self::Output {
		let rhs: Checked::<u32> = rhs.and_then(|i| i.try_into().ok());
		self.zip_with(rhs, |i1, i2| <T as num_traits::CheckedShr>::checked_shr(&i1, i2))
	}
}


impl<T: Integer, Rhs: Integer + TryInto<u32>> core::ops::ShrAssign<Rhs> for Checked<T> {
	#[inline]
	fn shr_assign(&mut self, rhs: Rhs) {
		*self = <Checked<T> as core::ops::Shr<Rhs>>::shr(*self, rhs);
	}
}


impl<T: Integer, Rhs: Integer + TryInto<u32>> core::ops::ShrAssign<Checked<Rhs>> for Checked<T> {
	#[inline]
	fn shr_assign(&mut self, rhs: Checked<Rhs>) {
		*self = <Checked<T> as core::ops::Shr<Checked<Rhs>>>::shr(*self, rhs);
	}
}


#[test]
fn shr() {
}


impl<T: Integer + num_traits::CheckedNeg> num_traits::CheckedNeg for Checked<T> {
	#[inline]
	fn checked_neg(&self) -> Option<Self> {
		self
			.and_then(|i| <T as num_traits::ops::checked::CheckedNeg>::checked_neg(&i))
			.wrap_into_option()
	}
}


impl<T: Integer> num_traits::CheckedAdd for Checked<T> {
	#[inline]
	fn checked_add(&self, rhs: &Self) -> Option<Self> {
		<Checked<T> as core::ops::Add<Self>>::add(*self, *rhs).wrap_into_option()
	}
}


impl<T: Integer> num_traits::CheckedSub for Checked<T> {
	#[inline]
	fn checked_sub(&self, rhs: &Self) -> Option<Self> {
		<Checked<T> as core::ops::Sub<Self>>::sub(*self, *rhs).wrap_into_option()
	}
}


impl<T: Integer> num_traits::CheckedMul for Checked<T> {
	#[inline]
	fn checked_mul(&self, rhs: &Self) -> Option<Self> {
		<Checked<T> as core::ops::Mul<Self>>::mul(*self, *rhs).wrap_into_option()
	}
}


impl<T: Integer> num_traits::CheckedDiv for Checked<T> {
	#[inline]
	fn checked_div(&self, rhs: &Self) -> Option<Self> {
		<Checked<T> as core::ops::Div<Self>>::div(*self, *rhs).wrap_into_option()
	}
}


impl<T: Integer + num_traits::CheckedShl> num_traits::CheckedShl for Checked<T> {
	#[inline]
	fn checked_shl(&self, rhs: u32) -> Option<Self> {
		self
			.and_then(|i| <T as num_traits::CheckedShl>::checked_shl(&i, rhs))
			.wrap_into_option()
	}
}


impl<T: Integer + num_traits::CheckedShr> num_traits::CheckedShr for Checked<T> {
	#[inline]
	fn checked_shr(&self, rhs: u32) -> Option<Self> {
		self
			.and_then(|i| <T as num_traits::CheckedShr>::checked_shr(&i, rhs))
			.wrap_into_option()
	}
}


impl<T: Integer + num_traits::ops::overflowing::OverflowingAdd> num_traits::ops::overflowing::OverflowingAdd for Checked<T> {
	#[inline]
	fn overflowing_add(&self, rhs: &Self) -> (Self, bool) {
		let result = self
			.zip_with_inner(*rhs, |i1, i2| <T as num_traits::ops::overflowing::OverflowingAdd>::overflowing_add(&i1, &i2));

		match result {
			Some((v, flag)) => (Self::new(v), flag),
			None => (Self::ERROR, true),
		}
	}
}


impl<T: Integer + num_traits::ops::overflowing::OverflowingSub> num_traits::ops::overflowing::OverflowingSub for Checked<T> {
	#[inline]
	fn overflowing_sub(&self, rhs: &Self) -> (Self, bool) {
		let result = self
			.zip_with_inner(*rhs, |i1, i2| <T as num_traits::ops::overflowing::OverflowingSub>::overflowing_sub(&i1, &i2));

		match result {
			Some((v, flag)) => (Self::new(v), flag),
			None => (Self::ERROR, true),
		}
	}
}


impl<T: Integer + num_traits::ops::overflowing::OverflowingMul> num_traits::ops::overflowing::OverflowingMul for Checked<T> {
	#[inline]
	fn overflowing_mul(&self, rhs: &Self) -> (Self, bool) {
		let result = self
			.zip_with_inner(*rhs, |i1, i2| <T as num_traits::ops::overflowing::OverflowingMul>::overflowing_mul(&i1, &i2));

		match result {
			Some((v, flag)) => (Self::new(v), flag),
			None => (Self::ERROR, true),
		}
	}
}


impl<T: Integer + num_traits::SaturatingAdd> num_traits::SaturatingAdd for Checked<T> {
	#[inline]
	fn saturating_add(&self, rhs: &Self) -> Self {
		self.zip_with(*rhs, |i1, i2| Some(<T as num_traits::SaturatingAdd>::saturating_add(&i1, &i2)))
	}
}


impl<T: Integer + num_traits::SaturatingSub> num_traits::SaturatingSub for Checked<T> {
	#[inline]
	fn saturating_sub(&self, rhs: &Self) -> Self {
		self.zip_with(*rhs, |i1, i2| Some(<T as num_traits::SaturatingSub>::saturating_sub(&i1, &i2)))
	}
}


impl<T: Integer + num_traits::SaturatingMul> num_traits::SaturatingMul for Checked<T> {
	#[inline]
	fn saturating_mul(&self, rhs: &Self) -> Self {
		self.zip_with(*rhs, |i1, i2| Some(<T as num_traits::SaturatingMul>::saturating_mul(&i1, &i2)))
	}
}


impl<T: Integer + num_traits::WrappingNeg> num_traits::WrappingNeg for Checked<T> {
	#[inline]
	fn wrapping_neg(&self) -> Self {
		self.map(|i| <T as num_traits::WrappingNeg>::wrapping_neg(&i))
	}
}


impl<T: Integer + num_traits::WrappingAdd> num_traits::WrappingAdd for Checked<T> {
	#[inline]
	fn wrapping_add(&self, rhs: &Self) -> Self {
		self.zip_with(*rhs, |i1, i2| Some(<T as num_traits::WrappingAdd>::wrapping_add(&i1, &i2)))
	}
}


impl<T: Integer + num_traits::WrappingSub> num_traits::WrappingSub for Checked<T> {
	#[inline]
	fn wrapping_sub(&self, rhs: &Self) -> Self {
		self.zip_with(*rhs, |i1, i2| Some(<T as num_traits::WrappingSub>::wrapping_sub(&i1, &i2)))
	}
}


impl<T: Integer + num_traits::WrappingMul> num_traits::WrappingMul for Checked<T> {
	fn wrapping_mul(&self, rhs: &Self) -> Self {
		self.zip_with(*rhs, |i1, i2| Some(<T as num_traits::WrappingMul>::wrapping_mul(&i1, &i2)))
	}
}


impl<T: Integer + num_traits::WrappingShl + num_traits::CheckedShl> num_traits::WrappingShl for Checked<T> {
	#[inline]
	fn wrapping_shl(&self, rhs: u32) -> Self {
		self.map(|i| <T as num_traits::WrappingShl>::wrapping_shl(&i, rhs))
	}
}


impl<T: Integer + num_traits::WrappingShr + num_traits::CheckedShr> num_traits::WrappingShr for Checked<T> {
	#[inline]
	fn wrapping_shr(&self, rhs: u32) -> Self {
		self.map(|i| <T as num_traits::WrappingShr>::wrapping_shr(&i, rhs))
	}
}
