/*
 * SPDX-FileCopyrightText:  Copyright (C) 2024, Max Hahn
 * SPDX-License-Identifier: CERN-OHL-S-2.0
 *
 * This source describes Open Hardware and is licensed under the CERN-OHL-S v2.
 * You may redistribute and modify this source and make products using it under
 * the terms of the CERN-OHL-S v2 (https://ohwr.org/cern_ohl_s_v2.txt).
 *
 * This source is distributed WITHOUT ANY EXPRESS OR IMPLIED WARRANTY, INCLUDING
 * OF MERCHANTABILITY, SATISFACTORY QUALITY AND FITNESS FOR A PARTICULAR PURPOSE.
 * Please see the CERN-OHL-S v2 for applicable conditions.
 *
 * Source location: https://github.com/Mixih/NAIL
 *
 * As per CERN-OHL-S v2 section 4, should you produce hardware based on this
 * source, you must where practicable maintain the Source Location visible in
 * the documentation for the Product or other products you make using this
 * source.
 *
 * You should have recieved a copy of the CERN-OHL-S v2.0 license along with
 * this file. If you did not recieve a copy of the aforementioned license, you
 * may obtain a copy at https://ohwr.org/cern_ohl_s_v2.txt.
 */

// slice operator convenience macros
`define SLICE(i, w) slc_top(i, 0, w):slc_bot(i, 0, w)
`define SLICE_O(i, off, w) slc_top(i, off, w):slc_bot(i, off, w)
`define SLICE_R(t, b, w) slc_top(t, 0, w):slc_bot(b, 0, w)
`define SLICE_RO(t, b, off, w) slc_top(t, off, w):slc_bot(b, off, w)

function automatic integer slc_top;
    input integer i;
    input integer off;
    input integer item_width;
    begin
        slc_top = (((i + 1) * item_width) - 1) + off;
    end
endfunction

function automatic integer slc_bot;
    input integer i;
    input integer off;
    input integer item_width;
    begin
        slc_bot = i * item_width + off;
    end
endfunction

// sign and zero extension / padding
`define S_EXT(n, w, n_w) {{((n_w) - (w)){n[(w) - 1]}}, n}
`define Z_EXT(n, w, n_w) {{((n_w) - (w)){1'b0}}, n}
`define Z_PAD(n) ({1'b0, (n)})

// Utility functions
function automatic is_pow_2;
    input integer n;
    begin
        is_pow_2 = n == 0 || (n & (n - 1)) == 0;
    end
endfunction

function automatic integer calc_div_fac;
    input integer in_hz;
    input integer target_hz;
    begin
        calc_div_fac = in_hz / target_hz;
    end
endfunction

function automatic validate_div_fac;
    input integer div_fac;
    input integer in_hz;
    input integer target_hz;
    input integer tolerance_100ths_perc;
    begin : val_div_fac_scope
        if ((((in_hz / div_fac) - target_hz) * 10000) / target_hz > tolerance_100ths_perc
            || (((in_hz / div_fac) - target_hz) * 10000) / target_hz < -tolerance_100ths_perc)
            validate_div_fac = 1'b0;
        else
            validate_div_fac = 1'b1;
    end
endfunction
