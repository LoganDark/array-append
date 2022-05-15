# `array-append`

`array-append` exports a small family of functions for working with
const-generic array types:

- `concat` which concatenates two arrays
- `push_right` and `push_left` which add an element to the end or
  beginning of an array respectively
- `split` and `split_end` which split an array into two arrays
- `pop_right` and `pop_left` which separate the last or first element
  respectively from an array

And a few aliases:

- `push`/`pop` for `push_right`/`pop_right` respectively
- `unshift`/`shift` for `push_left`/`pop_left` respectively

This library requires a nightly compiler due to the use of
`#![feature(generic_const_exprs)]`. All unsafe code has been verified to be
sound by manual proof and Miri.

This library does not yet require the standard library, but it is brought in
anyway unless the `std` default feature is disabled. This is for
forward-compatibility in case `std`-dependent code is ever added.

## Example

Create a no-alloc builder:

```rust
#![allow(incomplete_features)]
#![feature(generic_const_exprs)]

use array_append::push;

#[derive(PartialEq, Debug)]
struct Built<const N: usize> {
	whatever: [usize; N]
}

struct Builder<const N: usize> {
	whatever: [usize; N]
}

impl Builder<0> {
	pub fn new() -> Self {
		Self { whatever: [] }
	}
}

impl<const N: usize> Builder<N> {
	pub fn from_array(array: [usize; N]) -> Self {
		Self { whatever: array }
	}

	pub fn with_usize(self, new: usize) -> Builder<{N + 1}> {
		// Can't use `Self` here, because `Self` is `Builder<N>`
		Builder { whatever: push(self.whatever, new) }
	}

	pub fn build(self) -> Built<N> {
		Built { whatever: self.whatever }
	}
}

assert_eq!(
	Builder::new()
		.with_usize(1)
		.with_usize(2)
		.with_usize(3)
		.build(),
	Builder::from_array([1, 2, 3]).build()
);
```
