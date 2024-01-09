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
 * True Dual-Port Block RAM
 *
 * This is a true block RAM template that maps well to FPGA RAM primitives, with
 * independent clock drive for each port as supported by Xilinx and Altera Block-RAM
 * primitives. The requested capacity must be a power of two to ensure correct device
 * primitive mapping reports on the Xilinx Vivado synthesizer.
 *
 * Xilinx device detail: The RAM is configured to be in no-change mode for optimal
 * performance, i.e. a read on the same clock cycle as a write will retrieve the previous
 * data in the block RAM. Plan accordingly.
 *
 * Tested for correct device mapping on:
 * - Xilinx Vivado synthesis
 */
module tdpbram #(
    parameter DATA_W = 8,
    parameter SIZE = 256,
    parameter PIPELINE_MODE = "PERFORMANCE",
    localparam ADDR_W = $clog2(SIZE)
) (
    input wire clka,
    input wire wea,
    input wire [ADDR_W - 1:0] addra,
    input wire [DATA_W - 1:0] dina,
    output wire [DATA_W - 1:0] douta,
    input wire clkb,
    input wire web,
    input wire [ADDR_W - 1:0] addrb,
    input wire [DATA_W - 1:0] dinb,
    output wire [DATA_W - 1:0] doutb
);
    `include "util.vh"

    generate
        if (PIPELINE_MODE != "PERFORMANCE" && PIPELINE_MODE != "LOW_LATENCY") begin
            : validate_pipeline_mode_param
            $error("Invalid PIPELINE_MODE param.");
        end
        if (!is_pow_2(SIZE)) begin : validate_size_param
            $warning("SIZE param is not a power of two. Synthesis report bugs may be encountered.");
        end
    endgenerate

    reg [DATA_W - 1:0] mem [0:SIZE - 1];
    reg [DATA_W - 1:0] douta_int;
    reg [DATA_W - 1:0] doutb_int;

    always @(posedge clka) begin : porta
        if (wea)
            mem[addra] <= dina;
        douta_int <= mem[addra];
    end

    always @(posedge clkb) begin : portb
        if (web)
            mem[addrb] <= dinb;
        doutb_int <= mem[addrb];
    end

    generate
        if (PIPELINE_MODE == "PERFORMANCE") begin : gen_mode_perf
            reg [DATA_W - 1:0] douta_ff;
            reg [DATA_W - 1:0] doutb_ff;
            assign douta = douta_ff;
            assign doutb = doutb_ff;
            always @(posedge clka) begin
                douta_ff <= douta_int;
            end
            always @(posedge clkb) begin
                doutb_ff <= doutb_int;
            end
        end else if (PIPELINE_MODE == "LOW_LATENCY") begin : gen_mode_ll
            assign douta = douta_int;
            assign doutb = doutb_int;
        end
    endgenerate

endmodule
