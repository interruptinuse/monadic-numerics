#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(feature = "try_trait", feature(try_trait_v2))]


mod checked;
mod traits;


pub use prelude::*;


pub mod prelude {
	pub use crate::checked::Checked;
	pub use crate::traits::Integer;
}
