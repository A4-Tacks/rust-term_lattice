use std::{
    fmt::{
        self,
        Display,
    },
    cell::{
        RefCell,
        RefMut,
    },
};
use enum_variant_eq::{
    EnumVariantEq,
    enum_variant_eq_derive::*,
};


pub mod consts {
    pub const ESC: char = '\x1b';
    pub const UNIT_COLOR_CHARS: usize = 18; // 平均一个颜色所消耗字符
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
}
use traits::*;


macro_rules! is_pat {
    ( $a:expr , $p:pat ) => (if let $p = $a { true } else { false });
}




#[derive(Clone, Copy)]
pub struct Config {
    pub half: char,
    pub default_color: Color,
    pub chromatic_aberration: u32,
}
impl Config {
    pub fn new() -> Self {
        Self {
            half: '▄',
            default_color: Color::None,
            chromatic_aberration: 0,
        }
    }
}


#[derive(Clone, Copy, Debug)]
struct Direction {
    pub len: u16,
    pub direction: char,
}
impl Direction {
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
impl Display for Direction {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let res = match self.len {
            0 => String::new(),
            1 => format!("{ESC}[{}", self.direction),
            _ => format!("{ESC}[{}{}", self.len, self.direction),
        };
        write!(f, "{res}")
    }
}
impl From<char> for Direction {
    fn from(d: char) -> Self {
        Self { len: 0, direction: d }
    }
}

#[cfg(test)]
mod direction_tests {
    use super::*;
    #[test]
    fn test() {
        let mut a = Direction::new();
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
struct ANSIColor {
    pub colors: Vec<u8>,
}
impl ANSIColor {
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
impl<T> From<T> for ANSIColor 
    where T: IntoIterator<Item = u8>
{
    fn from(x: T) -> Self {
        let mut res = Self::new();
        res.add(x);
        res
    }
}
impl Display for ANSIColor {
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
    use super::{ANSIColor,ESC};
    #[test]
    fn new() {
        assert_eq!(ANSIColor::new(), ANSIColor { colors: Vec::new() });
    }
    #[test]
    fn add() {
        let mut a = ANSIColor::new();
        a.add([1, 2, 4]);
        assert_eq!(a, ANSIColor { colors: Vec::from([1, 2, 4])})
    }
    #[test]
    fn from() {
        assert_eq!(ANSIColor::from([1, 2, 4]),
            ANSIColor { colors: vec![1, 2, 4]});
    }
    #[test]
    fn fmt() {
        let mut a = ANSIColor::new();
        a.add([1, 2, 4]);
        assert_eq!(format!("{a}"), format!("{ESC}[1;2;4m"));
        assert_eq!(format!("{}", ANSIColor::new()), String::new());

        let mut a = ANSIColor::new();
        a.add([49, 39]);
        assert_eq!(format!("{a}"), format!("{ESC}[0m"));
        let mut a = ANSIColor::new();
        a.add([39, 49]);
        assert_eq!(format!("{a}"), format!("{ESC}[0m"));
        let mut a = ANSIColor::new();
        a.add([8, 39, 49]);
        assert_eq!(format!("{a}"), format!("{ESC}[0m"));
    }
}


#[derive(Debug, Clone, Copy, PartialEq, Eq, EnumVariantEq)]
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
pub struct ScreenBuffer {
    pub colors: RefCell<Vec<Color>>,
    pub background_colors: RefCell<Vec<Color>>,
    /// 上一个输出的颜色 #0:bg #1:fg
    pub prev_color: RefCell<[Color; 2]>,
    size: Position,
    pub cfg: Config,
}
impl ScreenBuffer {
    /// # Examples
    /// ```
    /// # use term_lattice::{ScreenBuffer};
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
        };
        res.init_colors();
        res.init_bg_colors();
        res
    }
    /// get size
    pub fn size(&self) -> Position { self.size }
    /// 获取位置对应的存储下标
    fn get_pos_index(&self, pos: Position) -> usize {
        debug_assert!(pos[0] < self.size[0]);
        debug_assert!(pos[1] < self.size[1]);
        (pos[1] * self.size[0] + pos[0]) as usize
    }
    /// get position color
    pub fn get(&self, pos: Position) -> Color {
        self.colors.borrow()[self.get_pos_index(pos)]
    }
    /// set position color
    pub fn set(&self, pos: Position, color: Color) {
        self.colors.borrow_mut()[self.get_pos_index(pos)] = color;
    }
    pub fn init_colors(&self) {
        let mut c: RefMut<Vec<Color>> = self.colors.borrow_mut();
        c.clear();
        c.fill_capacity(self.cfg.default_color);
        debug_assert_eq!(c.len(), c.capacity());
    }
    pub fn init_bg_colors(&self) {
        let mut c: RefMut<Vec<Color>> = self.background_colors.borrow_mut();
        c.clear();
        c.fill_capacity(Color::None);
        debug_assert_eq!(c.len(), c.capacity());
    }
    pub fn init_prev_color(&self) {
        *self.prev_color.borrow_mut() = [Color::None; 2];
    }
    fn color_similarity(&self, color1: &Color, color2: &Color) -> bool {
        color1.chromatic_aberration(color2) < self.cfg.chromatic_aberration
    }
    #[allow(unused)]
    fn get_pos_color(&self, pos: Position) -> (Color, bool) {
        self.get_idx_color(self.get_pos_index(pos))
    }
    /// 获取位置的颜色及是否与背景相似
    fn get_idx_color(&self, idx: usize) -> (Color, bool) {
        let colors = self.colors.borrow();
        let bgs = self.background_colors.borrow();
        let (color, bcolor) = (colors[idx], bgs[idx]);
        (color, self.color_similarity(&color, &bcolor))
    }
    /// 获取目标位置的一个字符, 如果应跳过则返回 None
    /// 会在输出时顺带设置背景色
    fn get_pos_text(&self, pos: Position) -> Option<String> {
        let (bidx, fidx) = (
            self.get_pos_index(pos),
            self.get_pos_index([pos[0], pos[1] + 1]));
        let ((bcolor, bcolor_sim_bg),
             (fcolor, fcolor_sim_bg))
            = (self.get_idx_color(bidx),
               self.get_idx_color(fidx));
        if bcolor_sim_bg && fcolor_sim_bg {
            return None; // skip this char
        }
        let mut prev_color = self.prev_color.borrow_mut();
        let mut res = ANSIColor::new();
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
        Some(format!("{res}{}", self.cfg.half))
    }
    /// Gets the string used to render the output.
    /// You must leave enough lines under the cursor before outputting
    /// the string.
    /// You can use discontinuous output to avoid changing the color
    /// between multiple outputs that can affect the output effect.
    pub fn flush(&self, is_continue: bool) -> String {
        let width: u32 = self.size[0];
        let line_size: usize = width as usize * (
            UNIT_COLOR_CHARS * 2 + self.cfg.half.len_utf8()) + 9;
        let line_count = self.size[1];
        let text_line_count = line_count >> 1;
        let res_cap = line_size * (text_line_count + 1) as usize;
        let mut downs = Direction::from('B');
        let mut skips = Direction::from('C');
        let mut res: String
            = String::with_capacity(res_cap);
        let mut backs = Direction::from('D');
        let mut line_buf: String = String::with_capacity(line_size);

        if ! is_continue {
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
            if skips.len() as u32 != width {
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
            let mut a = ANSIColor::new();
            a.add([0]);
            res.push_str(&a.to_string());
        }
        debug_assert_eq!(res.capacity(), res_cap);
        res
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

        let mut b = ANSIColor::new();
        b.add([48, 5, 78, 38, 5, 68]);
        assert_eq!(a.get_pos_text([0, 0]).unwrap(), format!("{b}▄"));
        let mut b = ANSIColor::new();
        b.add([0]);
        assert_eq!(a.get_pos_text([1, 0]).unwrap(), format!("{b}▄"));
    }

    #[test]
    fn flush() {
        let n = 100;
        let mut cfg = Config::new();
        cfg.default_color = Color::C256(15);
        cfg.chromatic_aberration = 1;
        let a = ScreenBuffer::new_from_cfg([n; 2], cfg);
        for i in 0..n {
            a.set([i; 2], Color::C256((i & 0xff) as u8));
            println!("\x1b[H{}", a.flush(false));
        }
        for i in 0..n {
            a.set([(12 + i) / 8, i], Color::C256((i & 0xff) as u8));
            a.set([i, (12 + i) / 8], Color::C256((i & 0xff) as u8));
            println!("\x1b[H{}", a.flush(true));
            //println!("{:?}", a.flush());
        }
        let mut i: f64 = 0.0;
        let mut j = 0;
        let n1 = (n >> 1) as f64;
        while i < 6.28 {
            a.set(
                [((i.cos() * 0.5) * n1 + n1) as u32,
                    ((i.sin() * 0.5) * n1 + n1) as u32],
                Color::C256(j));
            println!("\x1b[H{}", a.flush(true));
            i += 0.025;
            j += 1;
        }
        println!("\x1b[H{}", a.flush(false));
        let s = ScreenBuffer::new([0, 0]).flush(true);
        assert_eq!(s, String::from(""));
    }
}