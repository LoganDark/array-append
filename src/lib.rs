//! # `array-append`
//!
//! `array-append` exports a small family of functions for working with
//! const-generic array types:
//!
//! - [`concat`] which concatenates two arrays
//! - [`push_right`] and [`push_left`] which add an element to the end or
//!   beginning of an array respectively
//! - [`split`] and [`split_end`] which split an array into two arrays
//! - [`pop_right`] and [`pop_left`] which separate the last or first element
//!   respectively from an array
//!
//! And a few aliases:
//!
//! - [`push`]/[`pop`] for [`push_right`]/[`pop_right`] respectively
//! - [`unshift`]/[`shift`] for [`push_left`]/[`pop_left`] respectively
//!
//! This library requires a nightly compiler due to the use of
//! `#![feature(generic_const_exprs)]`. All unsafe code has been verified to be
//! sound by manual proof and Miri.
//!
//! This library does not yet require the standard library, but it is brought in
//! anyway unless the `std` default feature is disabled. This is for
//! forward-compatibility in case `std`-dependent code is ever added.
//!
//! ## Example
//!
//! Create a no-alloc builder:
//!
//! ```
//! #![allow(incomplete_features)]
//! #![feature(generic_const_exprs)]
//!
//! use array_append::push;
//!
//! #[derive(PartialEq, Debug)]
//! struct Built<const N: usize> {
//! 	whatever: [usize; N]
//! }
//!
//! struct Builder<const N: usize> {
//! 	whatever: [usize; N]
//! }
//!
//! impl Builder<0> {
//! 	pub fn new() -> Self {
//! 		Self { whatever: [] }
//! 	}
//! }
//!
//! impl<const N: usize> Builder<N> {
//! 	pub fn from_array(array: [usize; N]) -> Self {
//! 		Self { whatever: array }
//! 	}
//!
//! 	pub fn with_usize(self, new: usize) -> Builder<{N + 1}> {
//! 		// Can't use `Self` here, because `Self` is `Builder<N>`
//! 		Builder { whatever: push(self.whatever, new) }
//! 	}
//!
//! 	pub fn build(self) -> Built<N> {
//! 		Built { whatever: self.whatever }
//! 	}
//! }
//!
//! assert_eq!(
//! 	Builder::new()
//! 		.with_usize(1)
//! 		.with_usize(2)
//! 		.with_usize(3)
//! 		.build(),
//! 	Builder::from_array([1, 2, 3]).build()
//! );
//! ```

#![allow(incomplete_features)]
#![deny(missing_docs)]
#![deny(rustdoc::missing_doc_code_examples)]

#![cfg_attr(not(std), no_std)]
#![feature(generic_const_exprs)]

use core::mem::{ManuallyDrop, MaybeUninit};

pub use push_right as push;
pub use pop_right as pop;

pub use push_left as unshift;
pub use pop_left as shift;

/// Concatenates the given array `a` with the given other array `b`. Returns a
/// new array which contains all elements from `a` and `b`. No elements are
/// dropped, copied or cloned.
///
/// # Example
///
/// ```
/// # use array_append::concat;
/// #
/// let arr1 = [1usize, 2, 3, 4, 5];
/// let arr2 = [6, 7, 8, 9, 10];
/// let arr = concat(arr1, arr2);
///
/// assert_eq!(arr, [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]);
/// ```
pub fn concat<const N: usize, const M: usize, T>(a: [T; N], b: [T; M]) -> [T; N + M] where [(); N + M]: {
	unsafe {
		let mut uninit = MaybeUninit::<[T; N + M]>::uninit();

		let ptr = uninit.as_mut_ptr() as *mut T;
		(ptr as *mut [T; N]).write(a);
		(ptr.add(N) as *mut [T; M]).write(b);

		uninit.assume_init()
	}
}

/// Extends the given array `a` by the given element `b`. Returns a new array
/// which is the direct extension of `a` by `b`. No elements are dropped, copied
/// or cloned.
///
/// # Example
///
/// ```
/// # use array_append::push_right;
/// #
/// let arr = [1usize, 2, 3, 4];
/// let elem = 5;
/// let appended = push_right(arr, elem);
///
/// assert_eq!(appended, [1, 2, 3, 4, 5]);
/// ```
pub fn push_right<const N: usize, T>(a: [T; N], b: T) -> [T; N + 1] where [(); N + 1]: {
	concat(a, [b])
}

/// Extends the given element `b` by the given array `a`. Returns a new array
/// which is the direct extension of `a` by `b`. No elements are dropped, copied
/// or cloned.
///
/// # Example
///
/// ```
/// # use array_append::push_left;
/// #
/// let arr = [2usize, 3, 4, 5];
/// let elem = 1;
/// let prepended = push_left(arr, elem);
///
/// assert_eq!(prepended, [1, 2, 3, 4, 5]);
/// ```
pub fn push_left<const N: usize, T>(a: [T; N], b: T) -> [T; 1 + N] where [(); 1 + N]: {
	concat([b], a)
}

/// Splits the given array `a` at the given point `M`. Returns a tuple
/// containing two arrays where the first element is an array containing all
/// elements from `a[..M]` and the second element is an array containing all
/// elements from `a[M..]`. No elements are dropped, copied or cloned.
///
/// # Example
///
/// ```
/// # use array_append::split;
/// #
/// let arr = [1usize, 2, 3, 4, 5];
///
/// // Currently, the turbofish syntax is required. rustc still cannot infer
/// // them even if you fully annotate these variables' types.
/// let (left, right) = split::<5, 3, usize>(arr);
///
/// assert_eq!(left, [1, 2, 3]);
/// assert_eq!(right, [4, 5]);
/// ```
pub fn split<const N: usize, const M: usize, T>(a: [T; N]) -> ([T; M], [T; N - M]) where [(); N - M]: {
	unsafe {
		let a = ManuallyDrop::new(a);
		let ptr = a.as_ptr() as *const T;
		let mut left = MaybeUninit::<[T; M]>::uninit();
		let mut right = MaybeUninit::<[T; N - M]>::uninit();

		left.as_mut_ptr().write((ptr as *const [T; M]).read());
		right.as_mut_ptr().write((ptr.add(M) as *const [T; N - M]).read());

		(left.assume_init(), right.assume_init())
	}
}

/// Identical to [`split`], but splits starting from the end of the array, to
/// hopefully help with compiler proofs (in cases like [`pop_right`]).
///
/// # Example
///
/// ```
/// # use array_append::split_end;
/// #
/// let arr = [1usize, 2, 3, 4, 5];
/// let (left, right) = split_end::<5, 3, usize>(arr);
///
/// assert_eq!(left, [1, 2]);
/// assert_eq!(right, [3, 4, 5]);
/// ```
pub fn split_end<const N: usize, const M: usize, T>(a: [T; N]) -> ([T; N - M], [T; M]) where [(); N - M]: {
	unsafe {
		let a = ManuallyDrop::new(a);
		let ptr = a.as_ptr() as *const T;
		let mut left = MaybeUninit::<[T; N - M]>::uninit();
		let mut right = MaybeUninit::<[T; M]>::uninit();

		left.as_mut_ptr().write((ptr as *const [T; N - M]).read());
		right.as_mut_ptr().write((ptr.add(N - M) as *const [T; M]).read());

		(left.assume_init(), right.assume_init())
	}
}

/// Pops one element from the end of the given array `a`, returning the rest of
/// the array and the popped element in a tuple. No elements are dropped, copied
/// or cloned.
///
/// # Example
///
/// ```
/// # use array_append::pop_right;
/// #
/// let arr = [1usize, 2, 3, 4, 5];
/// let (arr, end) = pop_right(arr);
///
/// assert_eq!(arr, [1, 2, 3, 4]);
/// assert_eq!(end, 5);
/// ```
pub fn pop_right<const N: usize, T>(a: [T; N]) -> ([T; N - 1], T) {
	let (left, [right]) = split_end::<N, 1, T>(a);
	(left, right)
}

/// Identical to [`pop_right`], but pops from the left of the array instead.
///
/// # Example
///
/// ```
/// # use array_append::pop_left;
/// #
/// let arr = [1usize, 2, 3, 4, 5];
/// let (arr, start) = pop_left(arr);
///
/// assert_eq!(arr, [2, 3, 4, 5]);
/// assert_eq!(start, 1);
/// ```
pub fn pop_left<const N: usize, T>(a: [T; N]) -> ([T; N - 1], T) {
	let ([right], left) = split::<N, 1, T>(a);
	(left, right)
}
