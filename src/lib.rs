/*!
Dates suitable for working with time-series that use monthly or longer periods.

New periods can be constructed easily. For example,
```
# use periodic_date::{Period, Step};
pub const QUARTERLY: Period = Period { step: Step::Positive(3), offset: 0 };
```
*/

use {
    debug_err::{DebugErr, src},
    std::{cmp::Ordering, fmt},
};

pub const MONTHLY: Period = Period { step: Step::Positive(1), offset: 0 };
pub const BIMONTHLY: Period = Period { step: Step::Positive(2), offset: 0 };
pub const QUARTERLY: Period = Period { step: Step::Positive(3), offset: 0 };
pub const SEMIANNUAL: Period = Period { step: Step::Positive(6), offset: 0 };
pub const ANNUAL: Period = Period { step: Step::Positive(12), offset: 0 };
pub const BIANNUAL: Period = Period { step: Step::Positive(24), offset: 0 };
pub const FIVEYEAR: Period = Period { step: Step::Positive(60), offset: 0 };

pub const REVERSE_MONTHLY: Period = Period { step: Step::Negative(1), offset: 0 };

pub type Result<T> = std::result::Result<T, DebugErr>;

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Period {
    pub step: Step,
    pub offset: u8,
}

impl Period {
    /**
    ```
    # use periodic_date::{QUARTERLY, REVERSE_MONTHLY, Step};
    assert_eq!(QUARTERLY.step_len(), 3);
    assert_eq!(REVERSE_MONTHLY.step_len(), -1);
    ```
    */
    // test:
    pub fn step_len(&self) -> i32 { self.step.step_len() }

    /**
    Checks if ``Self`` is a subperiod of ``period``. For example,
    ```
    # use periodic_date::{ANNUAL, BIMONTHLY, QUARTERLY};
    assert!(QUARTERLY.is_subperiod(ANNUAL));
    assert!(!BIMONTHLY.is_subperiod(QUARTERLY));
    ```
    */
    // test:
    pub fn is_subperiod(&self, period: Period) -> bool {
        let s1 = self.step_len().unsigned_abs();
        let s2 = period.step_len().unsigned_abs();
        let o1 = self.offset as i32;
        let o2 = period.offset as i32;
        s1 != 0 && s2 % s1 == 0 && (o1 - o2) % (s1 as i32) == 0
    }
}

// An enum is used here to disallow the use of zero (which would iterate forever).
/// Use for constructing ``const`` periods.
///
/// For example  
/// ```
/// # use periodic_date::{Period, Step};
/// pub const QUARTERLY: Period = Period { step: Step::Positive(3), offset: 0 };
/// ```
#[derive(Clone, Copy, PartialEq)]
pub enum Step {
    Positive(u16),
    Negative(u16),
}

impl Step {
    // tested in Period::step_len doctest 
    // test:
    fn step_len(&self) -> i32 {
        match self {
            Step::Positive(step) => *step as i32,
            Step::Negative(step) => -(*step as i32),
        }
    }
}

impl fmt::Debug for Step {
    // test: step_debug_is_correct
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

impl fmt::Display for Step {
    // test: step_debug_is_correct
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Step::Positive(step) => write!(f, "{}", step),
            Step::Negative(step) => write!(f, "-{}", step),
        }
    }
}

impl PartialOrd for Step {
    // test: partial_cmp_on_step_is_correct
    fn partial_cmp(&self, other: &Step) -> Option<Ordering> {
        self.step_len().partial_cmp(&other.step_len())
    }
}

impl fmt::Display for Period {
    // test:
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Period(step: {}, offset: {})", self.step, self.offset)
    }
}    

#[derive(Clone, Copy, Eq, Ord, PartialEq, PartialOrd)]
pub struct Date(i32);

impl fmt::Display for Date {
    // test:
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}-{}", self.ym().0, self.ym().1)
    }
}    

impl fmt::Debug for Date {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Date")
         .field("y", &self.ym().0)
         .field("m", &self.ym().1)
         .finish()
    }
}

impl Date {

    // test: is_aligned_should_work
    pub fn is_aligned(&self, period: Period) -> bool {
        (self.0 - (period.offset as i32)) % period.step_len() == 0
    }

    pub fn option_aligned(&self, period: Period) -> Option<Date> {
        if (self.0 - (period.offset as i32)) % period.step_len() == 0 {
            Some(*self)
        } else {
            None
        }
    }

    pub fn try_aligned(&self, period: Period) -> Result<Date> {
        if (self.0 - (period.offset as i32)) % period.step_len() == 0 {
            Ok(*self) 
        } else {
            Err(src!("Date {} does not align with period {}.", self, period))
        }
    }

    /// Construct a date. The ``period`` argument provides a check that
    /// the constructed date is aligned with a given period.
    /// ```
    /// # use periodic_date::{Date, QUARTERLY};
    /// let date = Date::from_ym(2024, 4).unwrap();
    /// ```
    // test: from_ym_error
    pub fn from_ym(y: i32, m: u8) -> Result<Self> {
        if m > 12 || m == 0 {
            Err(src!("Expected month 1-12, not {}", m))?
        }
        let date = Date((y * 12) + (m as i32 - 1));
        Ok(date)
    }

    // test:
    pub fn ym(&self) -> (i32, u8) {
        let m = (self.0 % 12 + 1) as u8;
        let y = self.0 / 12_i32;
        (y, m)
    }

    // test: is_contiguous_date_should_work
    // test: is_contiguous_date_error_handling
    pub fn is_contiguous(&self, other: Date, period: Period) -> Result<bool> {
        if *self == other {
            Err(src!("Both dates are the same."))?
        }
        if !self.is_aligned(period) {
            Err(src!("Date {} is not aligned with period {}.", self, period))?
        }
        if !other.is_aligned(period) {
            Err(src!("Other date {} is not aligned with period {}.", other, period))?
        }
        Ok((self.0 - other.0).abs() / period.step_len() == 1)
    }
    
    #[must_use]
    // test: incr_by_should_work
    pub fn incr_by(&mut self, period: Period) -> Result<()> {
        if !self.is_aligned(period) {
            Err(src!("Date {} is not aligned with period {}.", self, period))?
        }
        self.0 += period.step_len();
        Ok(())
    }

    #[must_use]
    // test: decr_by_should_work
    pub fn decr_by(&mut self, period: Period) -> Result<()> {
        if !self.is_aligned(period) {
            Err(src!("Date {} is not aligned with period {}.", self, period))?
        }
        self.0 -= period.step_len();
        Ok(())
    }

    pub fn month_delta(&self, other: Date) -> i32 { other.0 - self.0 }

    pub fn as_index(&self) -> i32 { self.0 }

    pub fn from_index(index: i32) -> Self { Date(index) }

    // test: period_from_contiguous_should_work
    pub fn period_from_contiguous(&self, other: Date) -> Result<Period> {
        if *self == other {
            Err(src!("Dates must not be equal ({}).", self))?
        }
        let step = other.0 - self.0;
        let offset = (self.0 % step) as u8;
        if step > 0 {
            // A conversion from i32 to u16 happens here.
            Ok(Period { step: Step::Positive(step.try_into().unwrap()), offset })
        } else {
            // A conversion from i32 to u16 happens here.
            Ok(Period { step : Step::Negative(step.try_into().unwrap()), offset })
        }
    }
}

#[derive(Clone, Debug)]
pub struct DateIter {
    start: Date,
    period: Period,
    current: Date,
    end: Option<Date>,
}

impl DateIter {
    pub fn new(date: Date, period: Period) -> Result<DateIter> {
        if !date.is_aligned(period) {
            Err(src!("Date {} must be aligned with period {}.", date, period))?
        }
        Ok(DateIter {
            start: date,
            period,
            current: date,
            end: None,
        })
    }

    pub fn range(start: Date, end: Date, period: Period) -> Result<DateIter> {
        if start == end {
            Err(src!("Start date {} and end date {} must be different.", start, end))?
        }
        if !start.is_aligned(period) {
            Err(src!("Start date {} does not align with period {}.", start, period))?
        }
        if !end.is_aligned(period) {
            Err(src!("End date {} does not align with period {}.", end, period))?
        }
        // Have to ensure that we don't iterate away from the end date.
        match period.step {
            Step::Positive(_) => {
                if start > end {
                    Err(src!(
                        "Start date {} must be > end date {} for period with positive step.",
                        start,
                        end
                    ))?
                }
            },
            Step::Negative(_) => {
                if end > start {
                    Err(src!(
                        "Start date {} must be < end date {} for period with negative step.",
                        start,
                        end
                    ))?
                }
            },
        }
        Ok(DateIter {
            start,
            period,
            current: start,
            end: Some(end),
        })
    }

    // test:
    pub fn start(&self) -> Date { self.start }
    // test:
    pub fn end(&self) -> Option<Date> { self.end }
    // test:
    pub fn period(&self) -> Period { self.period }
    // test:
    pub fn current(&self) -> Date { self.current }
}

impl Iterator for DateIter {
    type Item = Date;

    // test: date_iter_range_forward_works
    // test: date_iter_range_backward_works
    fn next(&mut self) -> Option<Self::Item> {
        if let Some(end) = self.end {
            match self.period.step {
                Step::Positive(_) => { if self.current > end { return None } },
                Step::Negative(_) => { if self.current < end { return None } },
            }
        }
        let result = self.current;
        self.current.0 += self.period.step_len();
        Some(result)
    }    
}


// ---test

#[cfg(test)]
mod test {

    use crate::*;

    #[test]
    fn from_ym_error() {
        assert!(Date::from_ym(2024, 13).is_err());
    }

    #[test]
    fn is_contiguous_date_error_handling() {

        // (    is_err)
        let samples = vec![
            (2024, 1, 2024, 4, QUARTERLY, false),
            (2024, 1, 2024, 3, QUARTERLY, true),
            (2024, 1, 2424, 1, QUARTERLY, false),
        ];

        for (y1, m1, y2, m2, p, is_err) in samples {

            let date1 = Date::from_ym(y1, m1).unwrap();
            let date2 = Date::from_ym(y2, m2).unwrap();
            assert_eq!(date1.is_contiguous(date2, p).is_err(), is_err)
        }
    }

    #[test]
    fn is_contiguous_date_should_work() {

        let samples = vec![
            (2024, 1, 2024, 4, QUARTERLY, true),
            (2024, 1, 2024, 4, MONTHLY, false),
        ];

        for (y1, m1, y2, m2, p, yes) in samples {

            let date1 = Date::from_ym(y1, m1).unwrap();
            let date2 = Date::from_ym(y2, m2).unwrap();
            assert_eq!(date1.is_contiguous(date2, p).unwrap(), yes)
        }
    }

    #[test]
    fn period_from_contiguous_should_work() {
        let date1 = Date::from_ym(2024, 1).unwrap();
        let date2 = Date::from_ym(2024, 4).unwrap();
        assert_eq!(
            date1.period_from_contiguous(date2).unwrap(),
            Period { step: Step::Positive(3), offset: 0 }
        );

        let date1 = Date::from_ym(2023, 12).unwrap();
        let date2 = Date::from_ym(2024, 3).unwrap();
        assert_eq!(
            date1.period_from_contiguous(date2).unwrap(),
            Period { step: Step::Positive(3), offset: 2 }
        );
    }

    #[test]
    fn incr_by_should_work() {
        let mut date = Date::from_ym(2024, 4).unwrap();

        let _ = date.incr_by(QUARTERLY);
        assert_eq!(date.ym(), (2024, 7));

        let _ = date.incr_by(QUARTERLY);
        assert_eq!(date.ym(), (2024, 10));

        let _ = date.incr_by(QUARTERLY);
        assert_eq!(date.ym(), (2025, 1));
    }

    #[test]
    fn decr_by_should_work() {
        let mut date = Date::from_ym(2024, 4).unwrap();

        let _ = date.decr_by(QUARTERLY);
        assert_eq!(date.ym(), (2024, 1));

        let _ = date.decr_by(QUARTERLY);
        assert_eq!(date.ym(), (2023, 10));
    }

    #[test]
    fn is_aligned_should_work() {

        let samples = vec![
            (2023, 12, MONTHLY, true),
            (2023, 1, MONTHLY, true),
            (2023, 2, QUARTERLY, false),
        ];

        for (y, m, p, t) in samples {
            let date = Date::from_ym(y, m).unwrap();
            assert_eq!(date.is_aligned(p), t);
        }
    }

    #[test]
    fn period_equality() {
        assert_eq!(Period { step: Step::Positive(12), offset: 0 }, ANNUAL);
    }

    // Is there some way that we can set up a DateIter to iterate forever on a range?
    // Since the end condition is an inequality, the only way to do this would be to
    // make the iterator go in the other direction to the end date. So test that setting
    // up an iterator to go the other direction would always fail.
    #[test]
    fn range_date_iter_cannot_go_forever() {

        // Should error if dates are not ordered correctly.
        assert!(
            DateIter::range(
                Date::from_ym(2024, 2).unwrap(),
                Date::from_ym(2024, 1).unwrap(),
                MONTHLY,
            ).is_err()
        );

        // Should error if dates are not ordered correctly.
        assert!(
            DateIter::range(
                Date::from_ym(2024, 1).unwrap(),
                Date::from_ym(2024, 2).unwrap(),
                REVERSE_MONTHLY,
            ).is_err()
        );

        // Should error if start and end dates are the same,
        assert!(
            DateIter::range(
                Date::from_ym(2024, 1).unwrap(),
                Date::from_ym(2024, 1).unwrap(),
                MONTHLY,
            ).is_err()
        );
    }

    #[test]
    fn subperiods_should_work() {
        assert!(MONTHLY.is_subperiod(ANNUAL))
    }

    #[test]
    fn step_debug_is_correct() {
        assert_eq!(&format!("{:?}", Step::Positive(3)), "3");
        assert_eq!(&format!("{:?}", Step::Negative(5)), "-5");
    }

    #[test]
    fn partial_cmp_on_step_is_correct() {
        assert!(Step::Negative(1) > Step::Negative(2));
        assert!(Step::Positive(1) < Step::Positive(3));
        assert!(Step::Negative(999) < Step::Positive(1));
        assert!(Step::Positive(1) > Step::Negative(999));
    }

    #[test]
    fn date_iter_range_backward_works() {
        let start = Date::from_ym(2024, 10).unwrap();
        let end = Date::from_ym(2024, 1).unwrap();
        let period = Period {
            step: Step::Negative(3),
            offset: 0,
        };

        let dates: Vec<_> = DateIter::range(start, end, period)
            .unwrap()
            .collect();

        assert_eq!(
            dates,
            vec![
                Date::from_ym(2024, 10).unwrap(),
                Date::from_ym(2024, 7).unwrap(),
                Date::from_ym(2024, 4).unwrap(),
                Date::from_ym(2024, 1).unwrap(),
            ]
        );
    }

    #[test]
    fn date_iter_range_forward_works() {
        let start = Date::from_ym(2024, 1).unwrap();
        let end = Date::from_ym(2024, 10).unwrap();
        let period = Period {
            step: Step::Positive(3),
            offset: 0,
        };

        let dates: Vec<_> = DateIter::range(start, end, period)
            .unwrap()
            .collect();

        assert_eq!(
            dates,
            vec![
                Date::from_ym(2024, 1).unwrap(),
                Date::from_ym(2024, 4).unwrap(),
                Date::from_ym(2024, 7).unwrap(),
                Date::from_ym(2024, 10).unwrap(),
            ]
        );
    }
}
