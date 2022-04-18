#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(feature = "try_trait", feature(try_trait_v2))]


mod checked;
mod saturating;
mod traits;


pub use checked::Checked;
pub use saturating::Saturating;


pub mod prelude {
	pub use crate::checked::Checked;
	pub use crate::saturating::Saturating;
}
