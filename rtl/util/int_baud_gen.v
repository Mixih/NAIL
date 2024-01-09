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
`timescale 1ns / 1ps

/**
 * Integer-N baud strobe generator
 *
 * This is an integer-N baud strobe generate that can be used to trigger higher clocked
 * logic at the speed of the lower-clocked output process. This is handy for a variety of
 * serdes applications such as low-speed serial bus transceivers with oversampling,
 * 7 segments displays, and decimation engines. Please note that integral nature of the
 * division factor causes major restrictions on the synthesizable strobe frequencies, for
 * a wide range of syntheisable strobe fequencies with the trade off of extra jitter, see
 * the fracn_baud_gen module.
 *
 * The key properties of this module have been formally verified in SBY. See the FORMAL
 * block below for details.
 */
module int_baud_gen #(
    parameter DIV_FACTOR = 10,
    localparam CTR_W = $clog2(DIV_FACTOR)
) (
    input wire clk,
    input wire en,
    output wire stb,
    output wire [CTR_W - 1:0] baud_ctr
);
    generate
        if (DIV_FACTOR <= 0) begin : validate_div_factor
            $error("The division factor must be > 0.");
        end
    endgenerate

    reg [CTR_W - 1:0] ctr = 'b0;
    reg stb_int = 1'b0;
    reg ctr_next_is_end = 1'b0;

    assign stb = stb_int;
    assign baud_ctr = ctr;

    always @(posedge clk) begin
        if (en) begin
            ctr_next_is_end <= DIV_FACTOR == 1? 1'b1 : ctr == DIV_FACTOR - 2;
            if (ctr_next_is_end) begin
                ctr <= 'b0;
                stb_int <= 1'b1;
            end else begin
                ctr <= ctr + 1;
                stb_int <= 1'b0;
            end
        end else begin
            ctr <= 'b0;
            ctr_next_is_end <= 1'b0;
            stb_int <= 1'b0;
        end
    end

    ///////////////////////////////////////////////////////////////////////////
    ///////////////////////////////////////////////////////////////////////////
    // Formal verification block
    //
    // Verifies the following properties:
    // - Design can produce at least two consecutive strobes
    // - Design has the correct spacing between stobe signals (correctness)
    // - No strobe signals are generated if the baud generateor is disabled
    ///////////////////////////////////////////////////////////////////////////
    ///////////////////////////////////////////////////////////////////////////
    `ifdef FORMAL
        /////////////////////////////////////////////////////////
        // Observers and utility signals
        /////////////////////////////////////////////////////////
        // $past is undefined value until system reaches first tick. Generate this signal
        // for use with asserts that check $past
        reg f_past_valid = 1'b0;
        always @(posedge clk)
            f_past_valid <= 1'b1;

        // observers
        integer f_stb_ctr = 0;  // total strobes seen so far
        always @(posedge clk) begin
            if (stb)
                f_stb_ctr <= f_stb_ctr + 1;
        end

        /////////////////////////////////////////////////////////
        // Property Specification (contract)
        /////////////////////////////////////////////////////////
        always @(posedge clk) begin : f_cover
            cover(stb == 1);       // strobe happen atleast one
            cover(f_stb_ctr == 2); // at least two strobes
        end

        always @(posedge clk) begin : f_edge_properties
            if (f_past_valid) begin
                // strobe pulses must be exactly one clock cycle
                if (DIV_FACTOR != 1) begin
                    assert(!stb || stb != $past(stb, 1));
                end
                // if not enabled, we should never generate strobe pulses
                if (!$past(en, 1))
                    assert(stb == 1'b0);
                // time between strobes should be DIV_FACTOR
                if (stb) begin
                    assert($past(baud_ctr, 1) == DIV_FACTOR - 1);
                end
            end
        end

    `endif
endmodule
