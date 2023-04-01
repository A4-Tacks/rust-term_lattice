Used to use ANSI output dot matrix drawing boards on terminals that support VT100. Due to the use of incremental output, it is very fast.
- Supports true color and 256 colors

Create a new color lattice at a fixed location and use incremental output to quickly refresh.

# Examples
```rust
use term_lattice::{Config,Color,ScreenBuffer};

let n = 100;
let mut cfg = Config::new();
cfg.default_color = Color::C256(15);
cfg.chromatic_aberration = 1;
let a = ScreenBuffer::new_from_cfg([n; 2], cfg);

for i in 0..n {
    a.set([i; 2], Color::C256((i & 0xff) as u8));
    println!("\x1b[H{}", a.flush(false));
}
```


# Panics
`The number of buffer rows must be an even number. found: {}`
## Examples
```rust
use term_lattice::ScreenBuffer;
ScreenBuffer::new([100, 101]);
```
