# hilbert16

Hilbert transforms between 1D and 2D space, optimized for u16 coordinates.

[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://github.com/ryanavella/hilbert16/blob/master/LICENSE-MIT) [![License: Unlicense](https://img.shields.io/badge/license-Unlicense-blue.svg)](https://github.com/ryanavella/hilbert16/blob/master/UNLICENSE) [![crates.io](https://img.shields.io/crates/v/hilbert16.svg?colorB=319e8c)](https://crates.io/crates/hilbert16) [![docs.rs](https://img.shields.io/badge/docs.rs-hilbert16-yellowgreen)](https://docs.rs/hilbert16)

![Hilbert](examples/hilbert.png)

# Examples

```rust
use hilbert16::{Curve, Point};

let order = 9;
let curve = Curve::new(order).unwrap();
            
let p = Point { x: 175, y: 295 };
println!("{:?} => {}", p, curve.dist_at(p).unwrap();
let d = 94_085;
println!("{} => {:?}", d, curve.point_at(d).unwrap();
```
