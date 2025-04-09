use crate::rutil::*;
use crate::{impl_register, impl_rw};

//NOTE: every line must end with `///` for doc, since the macro need deal with it
impl_register! {
    BANK0,
    0x00, 1, RO, WHO_AM_I(who_am_i) {/// Who am I register
        value, 0, 7, u8;/// Who am I value
    }
    0x01, 1, RO, REV_ID(rev_id) {/// Revision ID register
        value, 0, 7, u8;/// Revision ID value
    }
    0x02, 1, RW, CTRL(ctrl) {/// Control register
        test1, 0, 0, u8;/// Enable bit<br>0 - disable<br>1 - enable
        test2, 1, 3, u8;/// Mode bits
        test3, 4, 5, u8;/// Interrupt enable bit
        test4, 6, 6, u8;/// Reset bit
        test5, 7, 7, u8;/// Reserved bits
    }
}
