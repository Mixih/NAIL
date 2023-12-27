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

/*
 * 32x32b multiplier module, 6 pipeline stages.
 *
 * Designed for optimal implementation on devices that have 16x16 hardened
 * multipliers, with 3-stage internal pipelining and fused-MAC capabilities.
 * The design has been tested on the xilinx DSP48E1 blocks and closes timing
 * alone at 3.1ns on a XC7A100T-1 speed grade part.
 *
 * A partial formal proof targeted at Symbiyosys has been attached to this design.
 * Due to combinatorial explosion with multiplication-based designs, only a select
 * subset of inputs that are "interesting" have been chosen for the formal verification.
 *
 * Design parameters:
 *   - Latency: 6
 *   - Throughput: 1
 *   - 4 16x16 bit multipliers required for implementation
 */
module mul32x32 #(
    localparam IN_W = 32,
    localparam OUT_W = IN_W * 2
) (
    input wire clk,
    input wire en,
    input wire signed [IN_W - 1:0] a,
    input wire signed [IN_W - 1:0] b,
    output reg signed [OUT_W - 1:0] out = 'b0
);
    `include "util.vh"

    localparam LATENCY = 6;
    localparam MID = IN_W / 2;
    localparam [IN_W / 2 - 1:0] BIAS = 1 << (IN_W / 2 - 1);
    localparam [OUT_W - 1:0]  BIAS_SQ = 1 << ((IN_W - 1) * 2);

    // input registers
    reg [MID - 1:0] a_1 = 0;
    reg [MID - 1:0] a_0 = 0;
    reg [MID - 1:0] b_1 = 0;
    reg [MID - 1:0] b_0 = 0;
    // these are one bit larger to promote correct technology mapping
    reg [IN_W:0] z_1 = 0;
    reg [IN_W:0] a_1b_0 = 0;
    reg [IN_W:0] a_0b_1 = 0;
    // regular intermediates
    reg [IN_W - 1:0] a_1b_1 = 0;
    reg [IN_W - 1:0] a_0b_0 = 0;
    // extra bank of registers to allow the syntehsizer to infer MREG for chained mul-add
    // patterns
    reg [IN_W:0] a_1b_0_i = 0;
    reg [IN_W:0] a_0b_1_i = 0;
    reg [IN_W - 1:0] a_0b_0_i = 0;

    // this computes (z_2 << 32) + z_0 in the following order
    // i = z_2 + sbits(z_0)a, result = (i << 32) | z_0
    reg [OUT_W - 1:0] z_2pz_0_i = 0;
    reg [OUT_W - 1:0] z_2pz_0 = 0;
    reg [OUT_W - MID - 1:0] out_us_h = 0;
    reg [MID:0] out_l = 0;

    // register for correction factor calc
    reg signed [IN_W:0] signed_sum = 0;
    reg signed [OUT_W - 1:0] scaled_sum = 0;
    reg signed [OUT_W - 1:0] corr_f = 0;
    reg signed [OUT_W - 1:0] corr_f_reg1 = 0;
    reg signed [OUT_W - 1:0] corr_f_reg2 = 0;

    wire rst = ~en;

    always @(posedge clk) begin
        if (rst) begin
            a_1 <= 'b0;
            a_0 <= 'b0;
            b_1 <= 'b0;
            b_0 <= 'b0;
            a_0b_1_i <= 'b0;
            a_1b_0_i <= 'b0;
            a_0b_0 <= 'b0;
            a_0b_1 <= 'b0;
            a_1b_0 <= 'b0;
            a_1b_1 <= 'b0;
            z_1 <= 'b0;
            z_2pz_0_i <= 'b0;
            z_2pz_0 <= 'b0;
            out <= 'b0;
            signed_sum <= 'b0;
            scaled_sum <= 'b0;
            corr_f <= 'b0;
            corr_f_reg1 <= 'b0;
            corr_f_reg2 <= 'b0;
            out_us_h <= 'b0;
            out_l <= 'b0;
        end else if (en) begin
            // PS1: register inputs
            a_1 <= a[IN_W - 1:MID] + BIAS;
            a_0 <= a[MID - 1:0];
            b_1 <= b[IN_W - 1:MID] + BIAS;
            b_0 <= b[MID - 1:0];
            signed_sum <= `S_EXT(a, IN_W, IN_W + 1) + `S_EXT(b, IN_W, IN_W + 1);
            // PS2: calculate intermediates
            a_0b_0 <= a_0 * b_0;
            a_0b_1_i <= a_0 * b_1;
            a_1b_0_i <= a_1 * b_0;
            a_1b_1 <= a_1 * b_1;
            scaled_sum <= {signed_sum, {{(IN_W - 1){1'b0}}}};
            // PS3: extra register stage
            a_1b_0 <= a_1b_0_i;
            a_0b_1 <= a_0b_1_i;
            corr_f <= scaled_sum + BIAS_SQ;
            z_2pz_0_i <= {a_1b_1, a_0b_0};
            // PS4: calculate intermediate sums
            z_1 <= a_0b_1 + a_1b_0;
            corr_f_reg1 <= -corr_f;
            z_2pz_0 <= z_2pz_0_i;
            // PS5: final value
            out_us_h <= (`Z_EXT(z_1, IN_W + 1, OUT_W - MID)) + z_2pz_0[OUT_W - 1:MID];
            out_l <= {1'b0, z_2pz_0[MID - 1:0]} + corr_f_reg1[MID-1:0];
            corr_f_reg2 <= corr_f_reg1;
            // PS6 adjust output value
            out <= {out_us_h + corr_f_reg2[OUT_W - 1:MID] + `Z_EXT(out_l[MID], 1, OUT_W - MID),
                    out_l[MID-1:0]};
        end
    end

    // formal properties
    `ifdef FORMAL
        // observers
        integer f_ctr = 0;
        reg f_en_reg;
        reg signed [LATENCY*32 - 1:0] f_a_sr = 0;
        reg signed [LATENCY*32 - 1:0] f_b_sr = 0;

        // $past is undefined value until system reaches first tick. Generate this signal
        // for use with asserts that check $past
        reg f_past_valid = 1'b0;
        always @(posedge clk)
            f_past_valid <= 1'b1;

        // to make the proof viable, we only verify for sequences of select interesting inputs
        always @(*) begin : restrict_input_space
            assume(
                a == 'b0 || a == 'b1 || a == 32'hffffffff || a == 32'h7fffffff || a == 32'h80000000
                || a == 32'h55555555 || a == 32'haaaaaaaa || a == 32'hf0f0f0f0 || a == 32'h0f0f0f0f
                || a == 32'hff00ff00 || a == 32'h00ff00ff || a == 32'hffff0000 || a == 32'h0000ffff
                || a[28:4] == 'b0
                || (a[28:16] == 'b0 && a[11:0] == 'b0)
            );
            assume(
                b == 'b0 || b == 'b1 || b == 32'hffffffff || b == 32'h7fffffff || b == 32'h80000000
                || b == 32'h55555555 || b == 32'haaaaaaaa || b == 32'hf0f0f0f0 || b == 32'h0f0f0f0f
                || b == 32'hff00ff00 || b == 32'h00ff00ff || b == 32'hffff0000 || b == 32'h0000ffff
                || b[28:4] == 'b0
                || (b[28:16] == 'b0 && b[11:0] == 'b0)
            );
        end

        always @(posedge clk) begin : observers
            if (en) begin
                f_a_sr <= {f_a_sr[`SLICE_R(LATENCY - 2, 0, 32)], a};
                f_b_sr <= {f_b_sr[`SLICE_R(LATENCY - 2, 0, 32)], b};
                f_ctr <= f_ctr + 1;
            end else begin
                f_ctr <= 'b0;
                f_a_sr <= 'b0;
                f_b_sr <= 'b0;
            end
            f_en_reg <= en;
        end

        wire signed [63:0] f_expected_product = $signed(f_a_sr[`SLICE(LATENCY-1, 32)]) * $signed(f_b_sr[`SLICE(LATENCY-1,32)]);
        always @(posedge clk) begin : properties
            if (en) begin
                if (f_ctr >= LATENCY) begin
                    // check that the product is correct
                    assert(out == f_expected_product);
                end
                if (f_past_valid && f_ctr >= LATENCY + 4) begin
                    // check that the throughput of one mul/cycle is achievable
                    cover(out != $past(out, 1)
                        && $past(out, 1) != $past(out, 2)
                        && $past(out, 2) != $past(out, 3)
                        && $past(out, 3) != 0
                    );
                end
            end
            // check that the multiplier output reaches zero one or more cycles after the enable
            // is deasserted
            if (~f_en_reg) begin
                assert(out == 'b0);
            end
        end
    `endif
endmodule
