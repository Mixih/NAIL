/*
 * Copyright (C) 2023, Max Hahn
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
 * source, you must where practicable maintain the Source Location visible in the
 * documentation for the Product or other products you make using this source.
 *
 * You should have recieved a copy of the CERN_OHL-S v2 along with this file (see
 * ${REPO_ROOT}/LICENSE.txt). If you did not recieve a copy of the aforementioned license,
 * you may obtain a copy at https://ohwr.org/cern_ohl_s_v2.txt.
 */
`timescale 1ns / 1ps

/**
 * Seven segment display interface module
 *
 * This is a display driver module for a classic 7-segment display with multiplexed
 * anode/cathode. The polarity of the common and segments are configurable to account for
 * various drive transistor schemes, such as high-side driver and low-side drive
 * transistors. The minimum digit on time is 1ms, the maximum is 1000ms. Please note that
 * the on-time is constant per unit in the seven-segment display unit, so the on-time may
 * need to be reduced for displays with more units to maintain consistent persistence of
 * vision.
 *
 * Output ports:
 *   - Segments: 8 units, order {A, B, C, D, E, F, G, DP}
 *   - Common: DIGITS units, order Most sig -> least sig
 */
module seven_seg #(
    parameter DIGITS = 4,
    parameter COM_POLARITY = "ACTIVE_HIGH",
    parameter SEG_POLARITY = "ACTIVE_HIGH",
    parameter ICLK_HZ = 100_000_000,
    parameter DIG_ON_TIME_MS = 1
) (
    input wire clk,
    input wire [DIGITS*4 - 1:0] din,
    input wire [DIGITS - 1:0] dps,
    output reg data_latched = 0,
    output wire [7:0] seg,
    output wire [DIGITS - 1:0] com
);
    `include "util.vh"

    localparam CTR_W = $clog2(DIGITS);

    reg [6:0] dig_lut [0:15];
    initial begin : init_dig_lut
        dig_lut[0]  = 7'b1111110;
        dig_lut[1]  = 7'b0110000;
        dig_lut[2]  = 7'b1101101;
        dig_lut[3]  = 7'b1111001;
        dig_lut[4]  = 7'b0110011;
        dig_lut[5]  = 7'b1011011;
        dig_lut[6]  = 7'b1011111;
        dig_lut[7]  = 7'b1110000;
        dig_lut[8]  = 7'b1111111;
        dig_lut[9]  = 7'b1111011;
        dig_lut[10] = 7'b1110111;
        dig_lut[11] = 7'b0011111;
        dig_lut[12] = 7'b1001110;
        dig_lut[13] = 7'b0111101;
        dig_lut[14] = 7'b1001111;
        dig_lut[15] = 7'b1000111;
    end

    reg [3:0] din_reg [0:DIGITS - 1];
    reg [DIGITS - 1:0] dps_reg = 'b0;
    reg [CTR_W - 1:0] c_dig = 'b0;
    wire dig_stb;
    wire com_on_val;
    wire should_latch_data = dig_stb && `Z_PAD(c_dig) == (DIGITS - 1);


    int_baud_gen #(
        .DIV_FACTOR(calc_div_fac(ICLK_HZ, 1000 / DIG_ON_TIME_MS))
    ) gen_fs_i (
        .clk(clk),
        .en(1'b1),
        .stb(dig_stb),
        .baud_ctr()
    );

    generate
        if (COM_POLARITY == "ACTIVE_HIGH") begin : com_pol_low
            assign com_on_val = 1'b1;
        end else if (COM_POLARITY == "ACTIVE_LOW") begin : com_pol_low
            assign com_on_val = 1'b0;
        end else begin : com_pol_invalid
            $error("Invalid COM_POLARITY.");
        end
        if (SEG_POLARITY == "ACTIVE_HIGH") begin : seg_pol_high
            assign seg = {dig_lut[din_reg[c_dig]], dps_reg[c_dig]};
        end else if (SEG_POLARITY == "ACTIVE_LOW") begin : seg_pol_low
            assign seg = {~dig_lut[din_reg[c_dig]], ~dps_reg[c_dig]};
        end else begin : seg_pol_invalid
            $error("Invalid SEG_POLARITY.");
        end
    endgenerate

    always @(posedge clk) begin : calc_digit_ptr
        if (dig_stb) begin
            if (`Z_PAD(c_dig) == DIGITS - 1)
                c_dig <= 'b0;
            else
                c_dig <= c_dig + 1;
        end
    end

    always @(posedge clk) begin : dps_sr
        if (should_latch_data) begin
            data_latched <= 1'b1;
            dps_reg <= dps;
        end else begin
            data_latched <= 1'b0;
        end
    end

    genvar dig_i;
    generate
        for (dig_i = 0; dig_i < DIGITS; dig_i = dig_i + 1) begin : dig_reg
            assign com[dig_i] = (c_dig == dig_i)? com_on_val : ~com_on_val;
            always @(posedge clk) begin
                if (should_latch_data)
                    din_reg[dig_i] <= din[`SLICE(dig_i, 4)];
            end
        end
    endgenerate

    ///////////////////////////////////////////////////////////////////////////
    ///////////////////////////////////////////////////////////////////////////
    // Formal verification block
    //
    // DOES NOT VERIFY OUTPUT PATTERNS, but those are easy to verify with TBs
    //
    // Verifies the following properties:
    // - The output display value is latched once per scan
    ///////////////////////////////////////////////////////////////////////////
    ///////////////////////////////////////////////////////////////////////////
    `ifdef FORMAL
        /////////////////////////////////////////////////////////
        // Observers and utility signals
        /////////////////////////////////////////////////////////
        reg f_past_valid = 1'b0;
        always @(posedge clk)
            f_past_valid <= 1'b1;

        reg f_should_latch_data_reg = 0;
        reg f_dig_stb_reg = 0;
        integer latch_ctr = 0;
        always @(posedge clk) begin
            f_dig_stb_reg = dig_stb;
            f_should_latch_data_reg <= should_latch_data;
            if (data_latched)
                latch_ctr <= latch_ctr + 1;
        end

        /////////////////////////////////////////////////////////
        // Property Specification (contract)
        /////////////////////////////////////////////////////////
        always @(posedge clk) begin : f_props_cover
            cover(latch_ctr == 2);
        end

        always @(posedge clk) begin : f_props_clk_edge
            if (f_should_latch_data_reg)
                assert(data_latched == 1'b1);
            if (f_past_valid)
                assert((data_latched && data_latched != $past(data_latched, 1)) || ~data_latched);
        end

        always @(*) begin : f_props_always_true
            // only one common signal should be on at any clock tick
            if (COM_POLARITY == "ACTIVE_HIGH") begin
                assert($countones(com) == 1);
            end else if (COM_POLARITY == "ACTIVE_LOW") begin
                assert($countbits(com, 1'b0) == 1);
            end
        end

        always @(posedge clk) begin : f_stability_props
            if (f_past_valid && !$rose(f_dig_stb_reg)) begin
                assert($stable(seg));
                assert($stable(com));
            end
            if (f_past_valid && !$rose(data_latched)) begin
                assert($stable(dps_reg));
            end
        end

        genvar f_dig_stab_i;
        generate
            for (f_dig_stab_i = 0; f_dig_stab_i < DIGITS; f_dig_stab_i = f_dig_stab_i + 1) begin
                : f_gen_dig_stab
                always @(posedge clk) begin : f_dig_stability_props
                    if (f_past_valid && !$rose(data_latched)) begin
                        assert($stable(din_reg[f_dig_stab_i]));
                    end
                end
            end
        endgenerate

    `endif
endmodule
