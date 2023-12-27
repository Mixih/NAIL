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
 * Xoshiro256** 64-bit pseudo-random number generator
 *
 * WARNING: THIS IS NOT A CRYPTOGRAPHICALLY SERCURE RNG. DO NOT USE FOR CRYPTO.
 *
 * This is a random number generator from the Xoshiro family of PRNGs, with a 256-bit
 * state space, and 64 bit output. It uses a LFSR architecture, with the mul operator used
 * to introduce non-linear randomness. Due to its extensive use of shift and xor
 * primitives, it is well suited for integer hardware implementation.
 *
 * Please note that the recommended seed algorithm by the xoshiro authors is SplitMix64.
 * However, we have found it to be a poor choice for FPGA implemention, due to the
 * presence of 64-bit multiplier. The current PRNG state seed algorithm is suboptimal and
 * may exhibit linearity artifacting. It does however gurantee that the generator will not
 * start up in the all zeros state, which is irrecoverable.
 *
 * See: https://prng.di.unimi.it/ for the original paper and specifications written by
 * Blackman and Vigna.
 */
module xoshiro256ss (
    input wire clk,
    input wire en,
    input wire [63:0] seed,
    output wire rout_tready,
    output wire [63:0] rout_tdata
);
    localparam LATENCY = 2;

    reg [63:0] state [0:3];
    reg [63:0] out;
    reg [63:0] omul5;
    reg [LATENCY - 1:0] ready_sr;

    assign rout_tready = ready_sr[LATENCY - 1];
    assign rout_tdata = out;

    wire [63:0] xors3 = state[3] ^ state[1];
    wire [63:0] rol_omul5 = (omul5 >> 7) | (omul5 << (64 - 7));

    always @(posedge clk) begin : state_update
        if (en) begin
            state[0] <= state[0] ^ state[3] ^ (state[1] << 17);
            state[1] <= state[1] ^ state[2];
            state[2] <= state[2] ^ state[0];
            state[3] <= (xors3 >> 45) | (xors3 << (64 - 45));
        end else begin
            // TODO: Improve seeding algorithm
            state[0] <= seed[0] == 0? seed | 64'b1 : seed;
            state[1] <= seed;
            state[2] <= seed;
            state[3] <= seed;
        end
    end

    always @(posedge clk) begin : compute_out_pipeline
        if (en) begin
            omul5 <= (state[1] << 2) + state[1];
            out <= (rol_omul5 << 3) + rol_omul5;
        end
    end

    always @(posedge clk) begin
        ready_sr <= {ready_sr[LATENCY - 2:0], en};
    end

endmodule
