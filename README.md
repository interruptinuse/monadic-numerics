`monadic-numerics`: Ergonomic operator trait overrides
------------------------------------------------------
### Prior art
- `std::num::Wrapping`
- https://github.com/myrrlyn/surety (you should probably use this one)
- https://github.com/zeta12ti/Checked
- https://github.com/dpc/overflow-proof

### `Checked`: All arithmetics ops behave as if `checked_*`
`Checked<T>` is a newtype wrapper over `Option<T>`.  In case of error (overflow,
underflow, division by zero, etc), all arithmetic operators set the inner option
to `None`; `None` propagates, like IEEE754 NaN.

```rust
let offset: usize = buf_len
  .checked_add(block_length).ok_or(ArithmeticOverflow)?
  .checked_add(palette_length).ok_or(ArithmeticOverflow)?;

// ... simplifies to
use monadic_numerics::prelude::*;
let offset: usize =
  (Checked::<usize>::from(buf_len) + block_length + palette_length)
  .ok_or(ArithmeticOverflow)?;
```
