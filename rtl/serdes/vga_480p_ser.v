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
 * VGA 480p 60Hz serializer
 *
 * This is a 640 x 480 progressive video serial for the analogue vga standard that outputs
 * the serialized waveform and sync signals. An additional VideoDAC or R2R ladder is
 * requried at the output of this module to convert the digital 8b color signals to the
 * analogue color levels. Compliant with the video standards, the sync signals are idle
 * low.
 *
 * Since video sources care commonly fed from RAM blocks, this module has a configurable
 * pipeline delay parameter that will shift the pixel indices to align with the RAM and
 * chip crossing pipeline delays.
 *
 * This module has been tested with a 25.173Mhz clock generated on-chip from a 100Mhz
 * reference signal. Please note that the serializer runs at the VGA clock domain, so CDC
 * constructs may be necessary to get data from the processing side into the video side.
 */
module vga_480p_ser #(
    parameter ADDR_DATA_DELAY = 2
) (
    input wire clk_25_175M,
    input wire[23:0] pix_in,
    output wire[7:0] r_out,
    output wire[7:0] g_out,
    output wire[7:0] b_out,
    output wire hsync,
    output wire vsync,
    output reg data_latched = 1'b0,
    output reg[9:0] hidx = 10'b0,
    output reg[9:0] vidx = 10'b0
);
    // timing info for 480p serialization
    // line: hsync: 96, back_porch: 48, visible: 640, front_porch: 16
    localparam H_SYNC_CNT = 96;
    localparam H_BPORCH_CNT = 48;
    localparam H_VIS_CNT = 640;
    localparam H_FPORCH_CNT = 16;
    localparam H_TOTAL_CNT = H_SYNC_CNT + H_BPORCH_CNT + H_VIS_CNT + H_FPORCH_CNT;
    localparam H_START_CNT = H_SYNC_CNT + H_BPORCH_CNT;
    localparam H_END_CNT = H_START_CNT + H_VIS_CNT;
    // frame: sync: 2, back_porch: 33, visible: 480, front_porch: 10
    localparam V_SYNC_CNT = 2;
    localparam V_BPORCH_CNT = 33;
    localparam V_VIS_CNT = 480;
    localparam V_FPORCH_CNT = 10;
    localparam V_TOTAL_CNT = V_SYNC_CNT + V_BPORCH_CNT + V_VIS_CNT + V_FPORCH_CNT;
    localparam V_START_CNT = V_SYNC_CNT + V_BPORCH_CNT;
    localparam V_END_CNT = V_START_CNT + V_VIS_CNT;

    wire visible_next;
    wire[9:0] screen_h_idx;
    wire[9:0] screen_v_idx;

    reg visible_reg;
    reg[23:0] latched_pixel = 24'b0;
    reg[9:0] h_count = 10'b0;
    reg[9:0] v_count = 10'b0;



    // vga internal logic signals
    // need to shift the visible signal left by one due to the
    assign visible_next = h_count >= H_START_CNT - ADDR_DATA_DELAY
                     && h_count < H_END_CNT - ADDR_DATA_DELAY
                     && v_count >= V_START_CNT
                     && v_count < V_END_CNT;
    assign screen_h_idx = visible_next? h_count - H_START_CNT + 1: 10'b0;
    assign screen_v_idx = (v_count >= V_START_CNT && v_count < V_END_CNT)? v_count - V_START_CNT : 10'b0;
    // vga output signals
    assign hsync = h_count < H_SYNC_CNT? 1'b0 : 1'b1;
    assign vsync = v_count < V_SYNC_CNT? 1'b0 : 1'b1;
    assign b_out = visible_reg? latched_pixel[23:16] : 8'b0;
    assign g_out = visible_reg? latched_pixel[15:8] : 8'b0;
    assign r_out = visible_reg? latched_pixel[7:0] : 8'b0;

    // shift registers
    always @(posedge clk_25_175M) begin
        visible_reg <= visible_next;
    end
    // vga counters
    always @(posedge clk_25_175M) begin
        // handle h_count roll
        if (h_count + 1 == H_TOTAL_CNT) begin
            h_count <= 10'b0;
            // handle v_count roll
            if (v_count + 1 == V_TOTAL_CNT) begin
                v_count <= 10'b0;
            end else begin
                v_count <= v_count + 1;
            end
        end else begin
            h_count <= h_count + 1;
        end
    end
    // latch pixel and screen-space indices for output
    always @(posedge clk_25_175M) begin
        if (visible_next == 1'b1) begin
            data_latched <= 1'b1;
            latched_pixel <= pix_in;
            hidx <= screen_h_idx + ADDR_DATA_DELAY;
        end else begin
            data_latched <= 1'b0;
            hidx <= 10'b0;
        end
        vidx <= screen_v_idx;
    end
endmodule
