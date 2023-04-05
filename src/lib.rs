use std::{
    fmt::{
        self,
        Display,
    },
    cell::{
        RefCell,
        RefMut, Ref,
    },
};


pub mod consts {
    pub const ESC: char = '\x1b';
    pub const UNIT_COLOR_CHARS: usize = 18; // 平均一个颜色所消耗字符
    pub const EMPTY: char = ' ';
    pub const HALF: char = '▄';
    pub const UP_HALF: char = '▀';
}
use consts::*;

pub mod types {
    pub type Rgb = [u8; 3];
    pub type SizeType = u32;
    pub type Position = [SizeType; 2];
}
use types::*;

pub mod traits {
    pub trait FillCapacity<T> {
        fn fill_capacity(&mut self, target: T);
    }
    impl<T: Clone> FillCapacity<T> for Vec<T> {
        /// fill capacity
        /// # Examples
        /// ```
        /// # use term_lattice::traits::FillCapacity;
        /// let mut a = Vec::with_capacity(3);
        /// a.push(2);
        /// a.fill_capacity(3);
        /// assert_eq!(a, vec![2, 3, 3]);
        /// assert_eq!(a.len(), a.capacity());
        /// ```
        fn fill_capacity(&mut self, target: T) {
            for _ in 0..(self.capacity() - self.len()) {
                self.push(target.clone())
            }
        }
    }
    pub trait EnumVariantEq {
        fn enum_variant_eq(&self, other: &Self) -> bool;
    }
}
use traits::*;

mod tools {
    pub fn min<T: PartialOrd>(a: T, b: T) -> T {
        if a < b {
            a
        } else {
            b
        }
    }
}
use tools::*;

macro_rules! is_pat {
    ( $a:expr, $p:pat ) => (if let $p = $a { true } else { false });
}

/// use tuple swap a and b
macro_rules! tuple_swap {
    ( $a:ident, $b:ident ) => {
        ($a, $b) = ($b, $a);
    };
}
#[test]
fn tuple_swap_test() {
    let (mut a, mut b) = (1, 2);
    tuple_swap!(a, b);
    assert_eq!((a, b), (2, 1));
}

/// set variable to no init variable
macro_rules! no_init_var {
    ( $( $name:ident ),+ ) => {
        $(
            #[allow(unused)]
            let $name: ();
        )+
    };
}

/// Configurator used to configure its behavior
/// # Examples
/// ```
/// # use term_lattice::Config;
/// let mut cfg = Config::new();
/// cfg.chromatic_aberration = 1;
/// // pass
/// ```
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Config {
    /// Standard Half Height Characters
    pub half: char,
    /// Standard half height characters, but in the upper half
    pub up_half: char,
    /// Empty character, should be a transparent character
    pub empty: char,
    /// Color used for filling during initialization
    pub default_color: Color,
    /// Color difference threshold, with a value range of approximately 0 to 765
    pub chromatic_aberration: u32,
    /// Prevent it from being directly created
    _private: (),
}
impl Config {
    /// new
    /// # Examples
    /// ```
    /// # use term_lattice::Config;
    /// assert_eq!(Config::new(), Config::default());
    /// ```
    pub fn new() -> Self {
        Self::default()
    }
}
impl Default for Config {
    fn default() -> Self {
        Self {
            half: HALF,
            up_half: UP_HALF,
            empty: EMPTY,
            default_color: Color::None,
            chromatic_aberration: 0,
            _private: (),
        }
    }
}


/// Constant enumeration representing direction
/// # Examples
/// ```
/// # use term_lattice::Direction::*;
/// assert_eq!(Up as usize, 0);
/// assert_eq!(Down as usize, 1);
/// assert_eq!(Right as usize, 2);
/// assert_eq!(Left as usize, 3);
/// ```
#[derive(Debug)]
pub enum Direction {
    Up = 0,
    Down,
    Right,
    Left,
}
impl From<Direction> for char {
    /// # Examples
    /// ```
    /// # use term_lattice::Direction::*;
    /// assert_eq!(char::from(Up), 'A');
    /// assert_eq!(char::from(Down), 'B');
    /// assert_eq!(char::from(Right), 'C');
    /// assert_eq!(char::from(Left), 'D');
    /// ```
    fn from(value: Direction) -> Self {
        match value {
            Direction::Up => 'A',
            Direction::Down => 'B',
            Direction::Right => 'C',
            Direction::Left => 'D',
        }
    }
}


#[derive(Clone, Copy, Debug)]
struct ANSICursorControl {
    pub len: u16,
    pub direction: char,
}
impl ANSICursorControl {
    #[allow(unused)]
    pub fn new() -> Self {
        Self::from('C')
    }
    pub fn len(&self) -> u16 { self.len }
    pub fn is_empty(&self) -> bool { self.len() == 0 }
    pub fn clear(&mut self) {
        self.len = 0
    }
    pub fn clear_and_result(&mut self) -> String {
        let res = self.to_string();
        self.clear();
        res
    }
    pub fn add(&mut self) {
        self.addn(1)
    }
    pub fn addn(&mut self, num: u16) {
        debug_assert!(self.len <= u16::MAX - num);
        self.len += num
    }
    #[allow(unused)]
    pub fn sub(&mut self) {
        self.subn(1)
    }
    #[allow(unused)]
    pub fn subn(&mut self, num: u16) {
        debug_assert!(self.len >= num);
        self.len -= num
    }
}
impl Display for ANSICursorControl {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let res = match self.len {
            0 => String::new(),
            1 => format!("{ESC}[{}", self.direction),
            _ => format!("{ESC}[{}{}", self.len, self.direction),
        };
        write!(f, "{res}")
    }
}
impl From<char> for ANSICursorControl {
    fn from(d: char) -> Self {
        Self { len: 0, direction: d }
    }
}
impl From<Direction> for ANSICursorControl {
    fn from(value: Direction) -> Self {
        Self::from(char::from(value))
    }
}

#[cfg(test)]
mod ansi_cursor_control_tests {
    use super::*;
    #[test]
    fn test() {
        let mut a = ANSICursorControl::new();
        assert_eq!(a.to_string(), String::new());
        a.add();
        assert_eq!(a.to_string(), String::from("\x1b[C"));
        a.add();
        assert_eq!(a.to_string(), String::from("\x1b[2C"));
        a.add();
        assert_eq!(a.to_string(), String::from("\x1b[3C"));
        a.direction = 'A';
        assert_eq!(a.to_string(), String::from("\x1b[3A"));
    }
}


/// 一个颜色序列
#[derive(Clone, PartialEq, Eq, Debug)]
struct ANSIColors {
    pub colors: Vec<u8>,
}
impl ANSIColors {
    pub fn new() -> Self {
        Self { colors: Vec::new() }
    }
    #[allow(unused)]
    pub fn with_capacity(capacity: usize) -> Self {
        Self { colors: Vec::with_capacity(capacity) }
    }
    pub fn add(&mut self, nums: impl IntoIterator<Item = u8>) {
        for i in nums {
            self.colors.push(i)
        }
    }
}
impl<T> From<T> for ANSIColors 
    where T: IntoIterator<Item = u8>
{
    fn from(x: T) -> Self {
        let mut res = Self::new();
        res.add(x);
        res
    }
}
impl Display for ANSIColors {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fn func(a: u8, b: u8) -> bool {
            const EMPTY: (u8, u8) = (39, 49);
            (a, b) == EMPTY || (b, a) == EMPTY
        }
        let len = self.colors.len();
        let res = if len != 0 {
            let x = if self.colors[len - 1] == 0
                || (len >= 2 && func(
                        self.colors[len - 1], self.colors[len - 2])) {
                "0".to_string()
            } else {
                self.colors.iter()
                    .map(|x| x.to_string())
                    .collect::<Vec<String>>().join(";")
            };
            format!("{ESC}[{}m", x)
        } else { /* empty */ "".to_string() };
        write!(f, "{res}")
    }
}
#[cfg(test)]
mod ansi_colors_tests {
    use super::{ANSIColors,ESC};
    #[test]
    fn new() {
        assert_eq!(ANSIColors::new(), ANSIColors { colors: Vec::new() });
    }
    #[test]
    fn add() {
        let mut a = ANSIColors::new();
        a.add([1, 2, 4]);
        assert_eq!(a, ANSIColors { colors: Vec::from([1, 2, 4])})
    }
    #[test]
    fn from() {
        assert_eq!(ANSIColors::from([1, 2, 4]),
            ANSIColors { colors: vec![1, 2, 4]});
    }
    #[test]
    fn fmt() {
        let mut a = ANSIColors::new();
        a.add([1, 2, 4]);
        assert_eq!(format!("{a}"), format!("{ESC}[1;2;4m"));
        assert_eq!(format!("{}", ANSIColors::new()), String::new());

        let mut a = ANSIColors::new();
        a.add([49, 39]);
        assert_eq!(format!("{a}"), format!("{ESC}[0m"));
        let mut a = ANSIColors::new();
        a.add([39, 49]);
        assert_eq!(format!("{a}"), format!("{ESC}[0m"));
        let mut a = ANSIColors::new();
        a.add([8, 39, 49]);
        assert_eq!(format!("{a}"), format!("{ESC}[0m"));
    }
}


#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Color {
    Rgb(Rgb),
    C256(u8),
    None,
}
impl Color {
    /// 转换至颜色序列
    /// # Examples
    /// ```
    /// # use term_lattice::Color;
    /// let a = Color::C256(72);
    /// assert_eq!(a.to_ansi(false), vec![38, 5, 72]);
    /// assert_eq!(a.to_ansi(true), vec![48, 5, 72]);
    ///
    /// let a = Color::C256(12);
    /// assert_eq!(a.to_ansi(false), vec![94]);
    /// assert_eq!(a.to_ansi(true), vec![104]);
    ///
    /// let a = Color::C256(3);
    /// assert_eq!(a.to_ansi(false), vec![33]);
    /// assert_eq!(a.to_ansi(true), vec![43]);
    ///
    /// let a = Color::Rgb([8, 18, 28]);
    /// assert_eq!(a.to_ansi(false), vec![38, 2, 8, 18, 28]);
    /// assert_eq!(a.to_ansi(true), vec![48, 2, 8, 18, 28]);
    /// ```
    pub fn to_ansi(&self, is_background: bool) -> Vec<u8> {
        let head = if is_background { 48 } else { 38 };
        match self {
            Self::Rgb(rgb) => vec![head, 2, rgb[0], rgb[1], rgb[2]],
            Self::C256(x) => {
                if *x < 16 {
                    let mut n = if *x < 8 { x + 30 } else { x + 82 };
                    if is_background { n += 10; }
                    vec![n]
                } else {
                    vec![head, 5, *x]
                }
            },
            Self::None => vec![if is_background { 49 } else { 39 }],
        }
    }
    /// get chromatic aberration
    pub fn chromatic_aberration(&self, other: &Self) -> u32 {
        type ResNum = u32;
        if ! self.enum_variant_eq(other) {
            // 类型不同就直接返回最大
            return ResNum::MAX;
        }
        match self {
            // 无法比较值
            Self::None => {
                if is_pat!(other, Self::None) {
                    0 // 也是 None 则无差异
                } else {
                    ResNum::MAX
                }
            },
            Self::C256(n) => {
                if let Self::C256(o) = other {
                    let num = if *n < 16 && *o < 16 {
                        30
                    } else if *n < 16 || *o < 16 {
                        return ResNum::MAX; // 16色无法比较256色
                    } else {
                        6
                    };
                    ((*n as i16 - *o as i16).abs() * num) as ResNum
                } else { panic!() }
            }
            Self::Rgb(color) => {
                type Num = i32;
                macro_rules! sum {
                    ( $a:expr $(, $x:expr)* ) => ( $a $(+ $x)* );
                }
                macro_rules! fun {
                    ( $self:ident, $other:ident
                      => $(( $i:expr, $w:expr )),+ ) => {
                        (sum!($(
                            ($self[$i] as Num - $other[$i] as Num).pow(2) * $w
                        ),+) as f32).sqrt() as ResNum
                    }
                }
                let other = if let Self::Rgb(x) = other
                    { x } else { panic!() };
                fun!(color, other => (0, 3), (1, 4), (2, 2))
            },
        }
    }
}
impl Default for Color {
    /// Default value
    /// # Examples
    /// ```
    /// # use term_lattice::Color;
    /// assert_eq!(Color::default(), Color::None)
    /// ```
    fn default() -> Self {
        Self::None
    }
}
impl EnumVariantEq for Color {
    /// # Examples
    /// ```
    /// # use term_lattice::{Color,traits::EnumVariantEq};
    /// assert!(Color::None.enum_variant_eq(&Color::None));
    /// assert!(Color::C256(39).enum_variant_eq(&Color::C256(78)));
    /// assert!(Color::Rgb([89; 3]).enum_variant_eq(&Color::Rgb([23; 3])));
    /// assert!(Color::C256(39).enum_variant_eq(&Color::C256(39)));
    /// assert!(! Color::C256(8).enum_variant_eq(&Color::None));
    /// assert!(! Color::None.enum_variant_eq(&Color::C256(23)));
    /// assert!(! Color::Rgb([89; 3]).enum_variant_eq(&Color::C256(87)));
    /// assert!(! Color::C256(8).enum_variant_eq(&Color::Rgb([53; 3])));
    /// ```
    fn enum_variant_eq(&self, other: &Self) -> bool {
        macro_rules! matcher {
            ( $( $pat:pat ),+ $(,)? ) => {
                match self {
                    $(
                        $pat => is_pat!(other, $pat),
                    )+
                }
            };
        }
        matcher!(
            Self::Rgb(..),
            Self::C256(..),
            Self::None,
        )
    }
}


#[cfg(test)]
mod color_test {
    use super::Color;

    #[test]
    fn chromatic_aberration() {
        assert_eq!(Color::None.chromatic_aberration(&Color::None), 0);
        assert_ne!(Color::None.chromatic_aberration(&Color::C256(0)), 0);
        assert_ne!(Color::None.chromatic_aberration(&Color::C256(15)), 0);
        assert_eq!(Color::C256(98).chromatic_aberration(&Color::C256(98)), 0);
        assert_ne!(Color::C256(98).chromatic_aberration(&Color::C256(99)), 0);
    }
}


/// Create a new color lattice at a fixed location
/// and use incremental output to quickly refresh.
/// # Examples
/// ```
/// # use term_lattice::{Config,Color,ScreenBuffer};
/// let n = 100;
/// let mut cfg = Config::new();
/// cfg.default_color = Color::C256(15);
/// cfg.chromatic_aberration = 1;
/// let a = ScreenBuffer::new_from_cfg([n; 2], cfg);
/// for i in 0..n {
///     a.set([i; 2], Color::C256((i & 0xff) as u8));
///     println!("\x1b[H{}", a.flush(false));
/// }
/// ```
#[derive(Clone, Debug)]
pub struct ScreenBuffer {
    colors: RefCell<Vec<Color>>,
    /// Colors present in the output area
    background_colors: RefCell<Vec<Color>>,
    /// The value of this field should be the color of the last change.
    /// Subscript 0 is the background color, and subscript 1 is the foreground color
    prev_color: RefCell<[Color; 2]>,
    size: Position,
    /// config
    pub cfg: Config,
    _private: (),
}
impl ScreenBuffer {
    /// # Examples
    /// ```
    /// # use term_lattice::ScreenBuffer;
    /// let a = ScreenBuffer::new([3, 4]);
    /// ```
    pub fn new(size: Position) -> Self {
        Self::new_from_cfg(size, Config::new())
    }
    pub fn new_from_cfg(size: Position, cfg: Config) -> Self {
        if size[1] & 1 == 1 {
            panic!(concat!( /* 逻辑行数限制为偶数, 文本行数限制为整行 */
                    "The number of buffer rows must be an even number.",
                    "found: {}"), size[1])
        }
        let len: usize = (size[0] * size[1]) as usize;
        let res: ScreenBuffer
            = Self {
                colors: RefCell::new(Vec::with_capacity(len)),
                background_colors: RefCell::new(Vec::with_capacity(len)),
                prev_color: RefCell::new([Color::None; 2]),
                size,
                cfg,
                _private: (),
        };
        res.init_colors();
        res.init_bg_colors();
        res
    }
    /// get size
    pub fn size(&self) -> Position {
        self.size
    }
    /// get pos index
    /// expr: y * width + x
    /// # Examples
    /// ```
    /// # use term_lattice::ScreenBuffer;
    /// let a = ScreenBuffer::new([20, 30]);
    /// assert_eq!(a.get_pos_index([3, 4]), 83);
    /// ```
    pub fn get_pos_index(&self, pos: Position) -> usize {
        debug_assert!(pos[0] < self.size[0]);
        debug_assert!(pos[1] < self.size[1]);
        (pos[1] * self.size[0] + pos[0]) as usize
    }
    /// get position color
    pub fn get(&self, pos: Position) -> Color {
        self.get_idx(self.get_pos_index(pos))
    }
    /// get index color
    pub fn get_idx(&self, idx: usize) -> Color {
        self.colors.borrow()[idx]
    }
    /// set position color
    pub fn set(&self, pos: Position, color: Color) {
        self.set_idx(self.get_pos_index(pos), color)
    }
    /// set index color
    pub fn set_idx(&self, idx: usize, color: Color) {
        self.colors.borrow_mut()[idx] = color;
    }
    /// Using `color` fill Color Buffer
    pub fn fill(&self, color: Color) {
        let mut c: RefMut<Vec<Color>> = self.colors.borrow_mut();
        c.clear();
        c.fill_capacity(color);
        debug_assert_eq!(c.len(), c.capacity());
    }
    /// Using `color` fill rect Color Buffer
    pub fn fill_rect(&self, pos: Position, size: Position, color: Color) {
        for mut y in pos[1]..min(pos[1] + size[1], self.size[1]) {
            y *= self.size[0];
            for x in pos[0]..min(pos[0] + size[0], self.size[0]) {
                self.set_idx((y + x) as usize, color)
            }
        }
    }
    /// Using `self.cfg.default_color` Fill Color Buffer
    pub fn init_colors(&self) {
        self.fill(self.cfg.default_color)
    }
    /// Using `None` Fill Background Color Buffer
    pub fn init_bg_colors(&self) {
        let mut c: RefMut<Vec<Color>> = self.background_colors.borrow_mut();
        c.clear();
        c.fill_capacity(Color::None);
        debug_assert_eq!(c.len(), c.capacity());
    }
    /// Initialize the background buffer area of a rectangular area
    pub fn init_rect_bg(&self, pos: Position, size: Position) {
        for mut y in pos[1]..min(pos[1] + size[1], self.size[1]) {
            y *= self.size[0];
            for x in pos[0]..min(pos[0] + size[0], self.size[0]) {
                self.init_idx_bg((y + x) as usize)
            }
        }
    }
    /// Initialize background buffer at index
    pub fn init_idx_bg(&self, idx: usize) {
        self.background_colors.borrow_mut()[idx]
            = Color::None;
    }
    /// Initialize the background buffer at the specified location
    pub fn init_pos_bg(&self, pos: Position) {
        self.init_idx_bg(self.get_pos_index(pos))
    }
    /// Initialize the current color buffer
    pub fn init_prev_color(&self) {
        *self.prev_color.borrow_mut() = [Color::None; 2];
    }
    /// get prev_color ref
    pub fn get_prev_color(&self) -> Ref<[Color; 2]> {
        self.prev_color.borrow()
    }
    /// get prev_color mut ref
    pub fn get_prev_color_mut(&self) -> RefMut<[Color; 2]> {
        self.prev_color.borrow_mut()
    }
    /// 两颜色在此缓冲区是否判定为相似
    fn color_similarity(&self, color1: &Color, color2: &Color) -> bool {
        color1.chromatic_aberration(color2) < self.cfg.chromatic_aberration
    }
    /// 获取位置的颜色及是否与背景相似
    #[allow(unused)]
    fn get_pos_color_and_simbg(&self, pos: Position) -> (Color, bool) {
        self.get_idx_color_and_simbg(self.get_pos_index(pos))
    }
    /// 获取下标的颜色及是否与背景相似
    fn get_idx_color_and_simbg(&self, idx: usize) -> (Color, bool) {
        let colors = self.colors.borrow();
        let bgs = self.background_colors.borrow();
        let (color, bcolor) = (colors[idx], bgs[idx]);
        (color, self.color_similarity(&color, &bcolor))
    }
    /// 获取目标位置的一个字符, 如果应跳过则返回 None
    /// 会在输出时顺带设置背景缓冲区
    fn get_pos_text(&self, pos: Position) -> Option<String> {
        let (mut bidx, mut fidx) = (
            self.get_pos_index(pos),
            self.get_pos_index([pos[0], pos[1] + 1]));
        let ((mut bcolor, bcolor_sim_bg),
             (mut fcolor, fcolor_sim_bg))
            = (self.get_idx_color_and_simbg(bidx),
               self.get_idx_color_and_simbg(fidx));
        if bcolor_sim_bg && fcolor_sim_bg {
            return None; // skip this char
        }
        no_init_var!(bcolor_sim_bg, fcolor_sim_bg); // disabled var
        let char: char
            = if is_pat!(fcolor, Color::None) {
                if is_pat!(bcolor, Color::None) {
                    self.cfg.empty
                } else {
                    // 交换输出颜色, 并且交换背景缓冲区写入下标
                    tuple_swap!(bcolor, fcolor);
                    tuple_swap!(bidx, fidx);
                    self.cfg.up_half
                }
            } else {
                self.cfg.half
            };
        let mut prev_color = self.prev_color.borrow_mut();
        let mut res = ANSIColors::new();
        let (bsimp, fsimp) /* 是否与上一个颜色相似 */
            = (self.color_similarity(&bcolor, &prev_color[0]),
               self.color_similarity(&fcolor, &prev_color[1]));
        let mut bcolors = self.background_colors.borrow_mut();
        // if not similar prev color then add to result
        bcolors[bidx] = if ! bsimp {
            prev_color[0] = bcolor;
            res.add(bcolor.to_ansi(true));
            bcolor
        } else {
            prev_color[0]
        };
        bcolors[fidx] = if ! fsimp {
            prev_color[1] = fcolor;
            res.add(fcolor.to_ansi(false));
            fcolor
        } else {
            prev_color[1]
        };
        Some(format!("{res}{char}"))
    }
    /// Gets the string used to render the output.
    /// You must leave enough lines under the cursor before outputting
    /// the string.
    /// You can use discontinuous output to avoid changing the color
    /// between multiple outputs that can affect the output effect.
    pub fn flush(&self, is_continue: bool) -> String {
        let width: SizeType = self.size[0];
        let line_size: usize = width as usize * (
            UNIT_COLOR_CHARS * 2 + self.cfg.half.len_utf8()) + 9;
        let line_count = self.size[1];
        let text_line_count = line_count >> 1;
        let res_cap = line_size * (text_line_count + 1) as usize;
        let mut downs = ANSICursorControl::from('B');
        let mut skips = ANSICursorControl::from('C');
        let mut res: String
            = String::with_capacity(res_cap);
        let mut backs = ANSICursorControl::from('D');
        let mut line_buf: String = String::with_capacity(line_size);

        macro_rules! add_empty_color {
            () => {{
                let mut a = ANSIColors::new();
                a.add([0]);
                res.push_str(&a.to_string());
            }};
        }

        if ! is_continue {
            add_empty_color!();
            self.init_prev_color()
        }

        for line_num in (0..line_count).step_by(2) {
            for column_num in 0..width {
                if let Some(x) = self.get_pos_text([column_num, line_num]) {
                    if ! skips.is_empty() {
                        line_buf.push_str(&skips.to_string());
                        backs.addn(skips.len());
                        skips.clear();
                    }
                    backs.add();
                    line_buf.push_str(&x);
                } else {
                    skips.add();
                }
            }
            if skips.len() as SizeType != width {
                // 当完整的跳过一行时我们可以认为这一行为空
                res.push_str(&downs.clear_and_result())
            }
            skips.clear();
            line_buf.push_str(&backs.clear_and_result());
            downs.add();
            res.push_str(&line_buf);
            line_buf.clear();
        }
        res.push_str(&downs.to_string());
        if ! is_continue {
            add_empty_color!();
        }
        debug_assert_eq!(res.capacity(), res_cap);
        res
    }
    /// Get a borrow of the color buffer
    /// # Examples
    /// ```
    /// # use term_lattice::{ScreenBuffer,Color};
    /// let a = ScreenBuffer::new([2, 2]);
    /// a.set([0, 1], Color::C256(39));
    /// let b = a.get_colors_borrow().clone();
    /// assert_eq!(
    ///     b, vec![Color::None, Color::None, Color::C256(39), Color::None]);
    /// ```
    pub fn get_colors_borrow(&self) -> Ref<Vec<Color>> {
        self.colors.borrow()
    }
    /// Get a borrow of the background_colors buffer
    /// # Examples
    /// ```
    /// # use term_lattice::{ScreenBuffer,Color};
    /// let a = ScreenBuffer::new([2, 2]);
    /// a.set([0, 1], Color::C256(39));
    /// assert_eq!(a.get_bg_colors_borrow()[2], Color::None);
    /// a.flush(false);
    /// assert_eq!(a.get_bg_colors_borrow()[2], Color::C256(39));
    /// ```
    pub fn get_bg_colors_borrow(&self) -> Ref<Vec<Color>> {
        self.background_colors.borrow()
    }
}
impl Default for ScreenBuffer {
    /// # Examples
    /// ```
    /// # use term_lattice::ScreenBuffer;
    /// let a = ScreenBuffer::default();
    /// assert_eq!(a.size(), [80; 2]);
    /// ```
    fn default() -> Self {
        Self::new([80; 2])
    }
}
impl PartialEq for ScreenBuffer {
    /// Compare the size, configuration, and color buffer of `self` to `other` for equality
    /// ```
    /// # use term_lattice::{ScreenBuffer,Color};
    /// let a = ScreenBuffer::default();
    /// let b = ScreenBuffer::default();
    /// b.flush(true);
    /// assert_eq!(a, b);
    /// a.set([7, 8], Color::C256(48));
    /// assert_ne!(a, b);
    /// b.flush(true);
    /// assert_ne!(a, b);
    /// a.set([7, 8], Color::None);
    /// assert_eq!(a, b);
    /// ```
    fn eq(&self, other: &Self) -> bool {
        self.size == other.size
            && self.cfg == other.cfg
            && self.colors == other.colors
    }
}
impl Into<Vec<Color>> for ScreenBuffer {
    /// Into colors.
    /// # Examples
    /// ```
    /// # use term_lattice::{ScreenBuffer,Color};
    /// let a = ScreenBuffer::new([2, 2]);
    /// a.set([0, 1], Color::C256(39));
    /// let b: Vec<Color> = a.into();
    /// assert_eq!(
    ///     b, vec![Color::None, Color::None, Color::C256(39), Color::None]);
    /// ```
    fn into(self) -> Vec<Color> {
        self.colors.into_inner()
    }
}
impl<T> From<(Position, Config, T)> for ScreenBuffer
    where T: Iterator<Item = Color>
{
    /// From (size, cfg, iter)
    /// # Examples
    /// ```
    /// # use term_lattice::{ScreenBuffer,Color,Config};
    /// let a = ScreenBuffer::from((
    ///     [2, 2],
    ///     Config::new(),
    ///     vec![Color::None, Color::C256(39)].into_iter(),
    /// ));
    /// let b: Vec<Color> = a.into();
    /// assert_eq!(
    ///     b, vec![Color::None, Color::C256(39), Color::None, Color::None]);
    /// ```
    fn from(value: (Position, Config, T)) -> Self {
        let res = Self::new_from_cfg(value.0, value.1);
        let mut i = 0;
        for color in value.2 {
            res.set_idx(i, color);
            i += 1;
        }
        res
    }
}
impl<T> From<(Position, T)> for ScreenBuffer
    where T: Iterator<Item = Color>
{
    /// From (size, iter)
    /// # Examples
    /// ```
    /// # use term_lattice::{ScreenBuffer,Color,Config};
    /// let a = ScreenBuffer::from((
    ///     [2, 2],
    ///     vec![Color::None, Color::C256(39)].into_iter(),
    /// ));
    /// let b: Vec<Color> = a.into();
    /// assert_eq!(
    ///     b, vec![Color::None, Color::C256(39), Color::None, Color::None]);
    /// ```
    fn from(value: (Position, T)) -> Self {
        Self::from((value.0, Config::default(), value.1))
    }
}


#[cfg(test)]
mod screen_buffer_test {
    use super::*;

    #[test]
    fn get_pos_index() {
        let a = ScreenBuffer::new([9, 8]);
        assert_eq!(a.get_pos_index([4, 6]), 58);
        assert_eq!(a.get_pos_index([2, 7]), 65);
    }
    
    #[test]
    fn get_pos_text() {
        let a = ScreenBuffer::new([8, 8]);
        a.set([0, 0], Color::C256(78));
        a.set([0, 1], Color::C256(68));

        let mut b = ANSIColors::new();
        b.add([48, 5, 78, 38, 5, 68]);
        assert_eq!(a.get_pos_text([0, 0]).unwrap(), format!("{b}▄"));
        let mut b = ANSIColors::new();
        b.add([0]);
        assert_eq!(a.get_pos_text([1, 0]).unwrap(), format!("{b}{EMPTY}"));
    }

    #[test]
    #[ignore]
    fn flush() {
        let n = 100;
        let mut cfg = Config::new();
        cfg.default_color = Color::C256(15);
        cfg.chromatic_aberration = 1;
        let a = ScreenBuffer::new_from_cfg([n; 2], cfg);
        macro_rules! out {
            ($mode:expr) => {
                print!("\x1b[H\x1b[B  {}", a.flush($mode));
            };
        }
        for i in 0..n >> 1 {
            for j in 0..n {
                a.set([j, i], Color::None);
                out!(true);
            }
        }
        for i in 0..n {
            a.set([i; 2], Color::C256((i & 0xff) as u8));
            out!(true);
        }
        for i in 0..n {
            a.set([(12 + i) / 8, i], Color::C256((i & 0xff) as u8));
            a.set([i, (12 + i) / 8], Color::C256((i & 0xff) as u8));
            out!(true);
        }
        let mut i: f64 = 0.0;
        let mut j = 0;
        let n1 = (n >> 1) as f64;
        while i < 6.28 {
            a.set(
                [((i.cos() * 0.5) * n1 + n1) as SizeType,
                    ((i.sin() * 0.5) * n1 + n1) as SizeType],
                Color::C256(j));
            out!(true);
            i += 0.025;
            j += 1;
        }
        out!(false);
        println!("\x1b[5A&&&");
        a.init_rect_bg([0, n - 10], [3, 2]);
        out!(false);
        a.fill_rect([8, 7], [22; 2], Color::C256(84));
        out!(false);
        //for i in (0..=255).step_by(4) {
        //    a.fill(Color::C256(i));
        //    out!(false);
        //}
        let s = ScreenBuffer::new([0, 0]).flush(true);
        assert_eq!(s, String::from(""));
    }

    #[test]
    fn incremental_flush() {
        let mut a = ScreenBuffer::new([80; 2]);
        a.cfg.chromatic_aberration = 1;
        a.flush(false);
        a.set([6, 8], Color::C256(29));
        assert_eq!(a.flush(true),
            format!("\x1b[4B\x1b[6C\x1b[38;5;29m{}\x1b[7D\x1b[36B", UP_HALF));
        a.set([6, 9], Color::C256(12));
        assert_eq!(a.flush(true),
            format!("\x1b[4B\x1b[6C\x1b[48;5;29;94m{}\x1b[7D\x1b[36B", HALF));
    }
}
