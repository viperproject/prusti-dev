/// From time::display[0]::iso_week_days[0]

use prusti_contracts::*;

#[requires(0 <= yday && yday <= 365 * 5)]
#[requires(0 <= wday && wday <= 6)]
fn iso_week_days(yday: i32, wday: i32) -> i32 {
    /* The number of days from the first day of the first ISO week of this
    * year to the year day YDAY with week day WDAY.
    * ISO weeks start on Monday. The first ISO week has the year's first
    * Thursday.
    * YDAY may be as small as yday_minimum.
    */
    let iso_week_start_wday: i32 = 1;                     /* Monday */
    let iso_week1_wday: i32 = 4;                          /* Thursday */
    let yday_minimum: i32 = 366;
    /* Add enough to the first operand of % to make it nonnegative. */
    let big_enough_multiple_of_7: i32 = (yday_minimum / 7 + 2) * 7;

    yday - (yday - wday + iso_week1_wday + big_enough_multiple_of_7) % 7
        + iso_week1_wday - iso_week_start_wday
}

fn main() {}
