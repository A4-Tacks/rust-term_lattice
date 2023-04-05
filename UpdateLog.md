# v0.1.1
Optimized output display for `Color::None`
Increase the constant EMPTY for null character output

# v0.1.2
Modified failed but reasonable assertions

# v0.2.0
Modified some display sections, added some practical methods, and adjusted the visibility of some fields.

# v0.3.0
Revised the visibility of some fields again and added some methods

# v0.4.0
Added some useful methods, such as `get_colors_arrow` and `Into<Vec<Color>>`, to compensate for visibility changes in `self.colors`.
Can be easily created from `Iterator` (such as the colors field of a buffer of the same size))
Manually expand `EnumVariantEq` to reduce dependencies
