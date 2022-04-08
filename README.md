`monadic-numerics`: Ergonomic operator trait overrides
------------------------------------------------------
```rust
use monadic_numerics::prelude::*;
```

See also: `std::num::Wrapping`.

### `Checked`: All arithmetics ops behave as if `checked_*`

`Checked<T>` is a newtype wrapper over `Option<T>`.  In case of error (overflow,
underflow, division by zero, etc), all arithmetic operators set the inner option
to `None`.

```rust
let offset: usize = buf_len
  .checked_add(block_length).ok_or(ArithmeticOverflow)?
  .checked_add(palette_length).ok_or(ArithmeticOverflow)?;
```

... simplifies to

```rust
let offset: usize =
  (Checked::<usize>::from(buf_len) + block_length + palette_length)
  .into_inner()
  .ok_or(ArithmeticOverflow)?;
```

NOTE: I was in too deep when I found that prior art exists, has two implementations,
and almost the exact same API: https://github.com/zeta12ti/Checked, https://github.com/dpc/overflow-proof
