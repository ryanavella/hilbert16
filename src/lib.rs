#![no_std]
//! Hilbert transforms between 1D and 2D space, optimized for u16 coordinates.
//!
//! # Examples
//!
//! ```
//! use hilbert16::{Curve, Point};
//!
//! let order = 9;
//! let curve = Curve::new(order).unwrap();
//!             
//! let p = Point { x: 175, y: 295 };
//! println!("{:?} => {}", p, curve.dist_at(p).unwrap());
//!
//! let d = 94_085;
//! println!("{} => {:?}", d, curve.point_at(d).unwrap());
//! ```

/// A point type with `u16` coordinates.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct Point {
    pub x: u16,
    pub y: u16,
}

impl From<(u16, u16)> for Point {
    fn from(p: (u16, u16)) -> Self {
        Self { x: p.0, y: p.1 }
    }
}

impl From<[u16; 2]> for Point {
    fn from(p: [u16; 2]) -> Self {
        Self { x: p[0], y: p[1] }
    }
}

impl From<Point> for (u16, u16) {
    fn from(p: Point) -> (u16, u16) {
        (p.x, p.y)
    }
}

impl From<Point> for [u16; 2] {
    fn from(p: Point) -> Self {
        [p.x, p.y]
    }
}

impl Point {
    /// The point `(0, 0)`.
    pub const ORIGIN: Self = Self { x: 0, y: 0 };

    const fn swap_xy(self) -> Self {
        Self {
            x: self.y,
            y: self.x,
        }
    }

    const fn mirror_xy(self, n: u16) -> Self {
        Self {
            x: n - 1 - self.x,
            y: n - 1 - self.y,
        }
    }

    const fn rot(self, n: u16, rx: bool, ry: bool) -> Self {
        match (rx, ry) {
            (true, false) => self.mirror_xy(n).swap_xy(),
            (false, false) => self.swap_xy(),
            _ => self,
        }
    }

    const fn shift(self, s: u8, rx: bool, ry: bool) -> Self {
        Self {
            x: self.x + ((rx as u16) << s),
            y: self.y + ((ry as u16) << s),
        }
    }

    const fn rot_shift(self, s: u8, rx: bool, ry: bool) -> Self {
        self.rot(1 << s, rx, ry).shift(s, rx, ry)
    }
}

/// A psuedo-Hilbert curve.
///
/// This type is optimized for O(1) queries of arbitrary points or
/// distances *without* pre-calculating the curve.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Curve {
    num_pnts: u32,
    side_len: u16,
    order: u8,
}

impl Default for Curve {
    fn default() -> Self {
        Self::new(0).unwrap()
    }
}

impl Curve {
    /// Generate an iteration of the Hilbert curve with the given `order`.
    ///
    /// The largest supported order is 15, which corresponds a square of 32768 by 32768 units.
    ///
    /// # Examples
    ///
    /// ```
    /// use hilbert16::Curve;
    ///
    /// assert!(matches!(Curve::new(15), Some(_)));
    /// assert_eq!(Curve::new(16), None);
    /// ```
    #[must_use]
    pub fn new(order: u8) -> Option<Self> {
        1_u16.checked_shl(order.into()).map(|side_len| {
            let num_pnts = u32::from(side_len).pow(2);
            Self {
                num_pnts,
                side_len,
                order,
            }
        })
    }

    /// The Hilbert curve's order.
    ///
    /// # Examples
    ///
    /// ```
    /// use hilbert16::Curve;
    ///
    /// let curve = Curve::new(2).unwrap();
    /// assert_eq!(curve.order(), 2);
    /// ```
    #[must_use]
    pub const fn order(self) -> u8 {
        self.order
    }

    /// The side length of the Hilbert curve's enclosing square.
    ///
    /// # Examples
    ///
    /// ```
    /// use hilbert16::Curve;
    ///
    /// let curve = Curve::new(2).unwrap();
    /// assert_eq!(curve.side_len(), 4);
    /// ```
    #[must_use]
    pub const fn side_len(self) -> u16 {
        self.side_len
    }

    /// The number of points contained in the Hilbert curve.
    ///
    /// # Examples
    ///
    /// ```
    /// use hilbert16::Curve;
    ///
    /// let curve = Curve::new(2).unwrap();
    /// assert_eq!(curve.num_pnts(), 16);
    /// ```
    #[must_use]
    pub const fn num_pnts(self) -> u32 {
        self.num_pnts
    }

    /// Get the point corresponding to the given distance.
    ///
    /// # Examples
    ///
    /// ```
    /// use hilbert16::{Curve, Point};
    ///
    /// let curve = Curve::new(1).unwrap();
    /// let p = curve.point_at(2).unwrap();
    /// assert_eq!(p, Point { x: 1, y: 1 });
    /// ```
    #[must_use]
    pub fn point_at(self, d: u32) -> Option<Point> {
        (self.num_pnts - 1).checked_sub(d)?;
        Some(self.wrapping_point_at(d))
    }

    /// Get the distance corresponding to the given point.
    ///
    /// # Examples
    ///
    /// ```
    /// use hilbert16::Curve;
    ///
    /// let curve = Curve::new(1).unwrap();
    /// let dist = curve.dist_at((1u16, 1u16)).unwrap();
    /// assert_eq!(dist, 2);
    /// ```
    pub fn dist_at<P>(self, p: P) -> Option<u32>
    where
        P: Into<Point>,
    {
        self.dist_at_impl(p.into())
    }

    fn dist_at_impl(self, p: Point) -> Option<u32> {
        (self.side_len - 1).checked_sub(p.x)?;
        (self.side_len - 1).checked_sub(p.y)?;
        Some(self.wrapping_dist_at_impl(p))
    }

    /// Get the point corresponding to the given distance, wrapping back to `(0, 0)`.
    ///
    /// # Examples
    ///
    /// ```
    /// use hilbert16::{Curve, Point};
    ///
    /// let curve = Curve::new(1).unwrap();
    /// let pnt = curve.wrapping_point_at(6);
    /// assert_eq!(pnt, Point { x: 1, y: 1 });
    /// ```
    #[must_use]
    pub fn wrapping_point_at(self, d: u32) -> Point {
        let (p, _) = (0..self.order).fold((Point::ORIGIN, d), |(p, t), s| {
            let half = t / 2;
            let rx = half % 2 == 1;
            let ry = half % 2 != t % 2;
            let p = p.rot_shift(s, rx, ry);
            let t = t / 4;
            (p, t)
        });
        p
    }

    /// Get the distance corresponding to the given point, wrapping back to `0`.
    ///
    /// # Examples
    ///
    /// ```
    /// use hilbert16::Curve;
    ///
    /// let curve = Curve::new(1).unwrap();
    /// let dist = curve.wrapping_dist_at((3u16, 1u16));
    /// assert_eq!(dist, 2);
    /// ```
    pub fn wrapping_dist_at<P>(self, p: P) -> u32
    where
        P: Into<Point>,
    {
        self.wrapping_dist_at_impl(p.into())
    }

    fn wrapping_dist_at_impl(self, p: Point) -> u32 {
        let (d, _) = (0..self.order).rev().fold((0, p), |(d, p), s| {
            let rx = p.x & (1 << s) != 0;
            let ry = p.y & (1 << s) != 0;
            let p = p.rot(self.side_len, rx, ry);
            let t = (3 * u32::from(rx)) ^ u32::from(ry);
            let d = d + (t << (2 * s));
            (d, p)
        });
        d
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn various_hilbert_orders() {
        for order in 0..=8 {
            let curve = Curve::new(order).unwrap();
            let num_pnts = curve.num_pnts();
            let side_len = curve.side_len();
            for dist in 0..num_pnts {
                let p = curve.point_at(dist).unwrap();
                assert_eq!(dist, curve.dist_at(p).unwrap());
                assert!(p.x < side_len);
                assert!(p.y < side_len);
            }
        }
    }
}
