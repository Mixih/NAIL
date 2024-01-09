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
 * Low-level UART transmit interface, 8n1
 *
 * This is a configurable low-level UART transmit interface, with a strobe/busy
 * logic interface. It should be paired with a transmission fifo if more than
 * one bytes at a time needs to be scheduled for sending. The FIFO has been designed
 * for continuous transmission throughput, with no gaps between UART symbols.
 *
 * A full proof targeted at the Symbiyosys toolchain has been included in this
 * design. See the formal verification block below for details on what areas of
 * the design are currently proven.
 */
module uart_tx_ll_8n1 #(
    parameter ICLK_HZ = 100_000_000,
    parameter BAUD_RATE = 115_200,
    localparam PORT_W = 8
) (
    input wire clk,
    input wire send_stb,
    input wire [PORT_W - 1:0] din,
    output reg tx = 1'b1,
    output reg busy = 1'b0
);
    `include "util.vh"

    localparam DIV_FAC = calc_div_fac(ICLK_HZ, BAUD_RATE);

    generate
        if (!validate_div_fac(DIV_FAC, ICLK_HZ, BAUD_RATE, 100)) begin
            : validate_baud_tolerance
            $warning("Generated baud rate is out of tolerance by > 1%.");
        end
    endgenerate
    localparam DCTR_W = $clog2(PORT_W);

    localparam STATE_IDLE = 2'd0;
    localparam STATE_START = 2'd1;
    localparam STATE_DATA = 2'd2;
    localparam STATE_STOP = 2'd3;

    reg [1:0] state = STATE_IDLE;
    reg [PORT_W - 1:0] data_sr = 'b0;
    reg [DCTR_W - 1:0] ctr = 'b0;

    reg baud_en = 1'b0;
    wire baud_stb;
    wire [$clog2(DIV_FAC) - 1:0] baud_ctr;
    wire baud_stb_going_high = baud_ctr == DIV_FAC - 1;

    int_baud_gen #(
        .DIV_FACTOR(DIV_FAC)
    ) baud_gen_i (
        .clk(clk),
        .en(baud_en),
        .stb(baud_stb),
        .baud_ctr(baud_ctr)
    );

    always @(*) begin
        case (state)
            STATE_START:
                tx = 1'b0;
            STATE_DATA:
                tx = data_sr[0];
            STATE_STOP:
                tx = 1'b1;
            default:
                tx = 1'b1;
        endcase
    end

    always @(posedge clk) begin : uart_deserialize
        case (state)
            STATE_IDLE: begin
                if (send_stb) begin
                    state <= STATE_START;
                    busy <= 1'b1;
                    data_sr <= din;
                    baud_en <= 1'b1;
                end
            end
            STATE_START: begin
                if (baud_stb)
                    state <= STATE_DATA;
            end
            STATE_DATA: begin
                if (baud_stb) begin
                    ctr <= ctr + 1;
                    data_sr <= {1'b0, data_sr[PORT_W - 1:1]};
                    if (`Z_PAD(ctr) == PORT_W - 1) begin
                        state <= STATE_STOP;
                        ctr <= 'b0;
                    end
                end
            end
            STATE_STOP: begin
                if (baud_stb_going_high)
                    busy <= 1'b0;
                if (baud_stb) begin
                    // fast repeast with idle skip
                    if (send_stb) begin
                        state <= STATE_START;
                        data_sr <= din;
                        busy <= 1'b1;
                    // normal idle path
                    end else begin
                        state <= STATE_IDLE;
                        baud_en <= 1'b0;
                    end
                end
            end
        endcase
    end


    ///////////////////////////////////////////////////////////////////////////
    ///////////////////////////////////////////////////////////////////////////
    // formal verification block
    //
    // Verifies the following properties:
    // - Signal timings
    // - Serialization correctness
    // - TODO: Absolute cycle time stability verification to verify dividers
    ///////////////////////////////////////////////////////////////////////////
    ///////////////////////////////////////////////////////////////////////////
    `ifdef FORMAL
        `ifdef UART_RX_LL_8N1
            `define ASSUME assume
            `define MODULE_IS_FORMAL_TOP 1
        `else
            `define ASSUME assert
            `define MODULE_IS_FORMAL_TOP 0
        `endif

        /////////////////////////////////////////////////////////
        // Observers and utility signals
        /////////////////////////////////////////////////////////
        reg f_past_valid_i = 1'b0;
        reg f_past_valid = 1'b0;
        always @(posedge clk) begin
            f_past_valid_i <= 1'b1;
            f_past_valid <= f_past_valid_i;
        end

        integer f_istate_ctr = 0;
        integer f_trans_ctr = 0;
        integer f_sym_ctr = 0;
        integer t1_idle = 0;
        reg f_started = 1'b0;
        reg f_finished = 1'b0;
        // for correct verification we need a solver chosen constant byte of data to send
        (* anyconst *) reg [PORT_W - 1:0] f_data_val;

        always @(posedge clk) begin : f_gen_observers
            if (send_stb && !busy) begin
                f_started <= 1'b1;
                f_finished <= 1'b0;
                f_sym_ctr <= 1;
            end
            if (state == STATE_STOP && baud_stb_going_high) begin
                f_finished <= 1'b1;
                f_started <= 1'b0;
                f_sym_ctr <= 0;
                f_trans_ctr <= f_trans_ctr + 1;
            end
            if (f_trans_ctr == 1 && state == STATE_IDLE)
                t1_idle <= t1_idle + 1;
            if (f_started && baud_stb && state != STATE_STOP)
                f_sym_ctr <= f_sym_ctr + 1;
        end

        /////////////////////////////////////////////////////////
        // Property Specification (contract)
        /////////////////////////////////////////////////////////
        always @(posedge clk) begin : f_assumptions
            // used to setup the input asusmptions to prove correctness
            `ifdef MODULE_IS_FORMAL_TOP
                assume(din == f_data_val);
            `endif
        end

        always @(posedge clk) begin : f_cover_props
            // ensure that the state machine can finish at least once
            cover(f_finished == 1'b1);
            // ensure that transmitting once is possible
            cover(f_trans_ctr == 1);
            cover(f_trans_ctr == 2);
            cover(f_trans_ctr == 2 && t1_idle == 2);
        end

        always @(posedge clk) begin : f_stability_props
            if (f_past_valid && ~$rose($past(baud_stb)) && $past(state) != STATE_IDLE) begin
                // data and ready signals should not change if no strobe
                assert($stable(data_sr));
                assert($stable(tx));
            end
        end

        always @(*) begin : f_induction_props
            case(state)
                STATE_IDLE: begin
                    assert(ctr == 0);
                    assert(baud_en == 1'b0);
                    assert(f_sym_ctr == 0);
                    assert(!f_started);
                    assert(!busy);
                end
                STATE_START: begin
                    assert(ctr == 0);
                    assert(f_sym_ctr == 1);
                    assert(f_started);
                end
                STATE_DATA: begin
                    assert(f_sym_ctr == ctr + 2);
                    assert(f_sym_ctr >= 2 && f_sym_ctr <= 9);
                    assert(f_started);
                end
                STATE_STOP: begin
                    assert(ctr == 0);
                end
            endcase
        end

        always @(posedge clk) begin : f_state_props
            if (state == STATE_IDLE) begin
                // idle is HIGH
                assert(tx == 1'b1);
            end
            // if in the stop state but not the special repeat part, the state machine
            // must be started and the counter value must be PORT_W + 2
            if (f_past_valid && state == STATE_STOP && !$rose($past(baud_stb_going_high))) begin
                assert(f_started);
                assert(f_sym_ctr == PORT_W + 2);
            end
        end

        always @(posedge clk) begin : f_started_finished_props
            // uart transmission should consist of 10 symbols
            if (f_past_valid && $rose(f_finished))
                assert($past(f_sym_ctr) == PORT_W + 2);
            // can't be busy if finished
            if (f_finished)
                assert(busy == 1'b0);
            // must be busy if started
            if (f_started)
                assert(busy == 1'b1);
        end

        always @(posedge clk) begin : f_sym_ctr_props
            if (f_sym_ctr == 1) begin
                // first symbol (start bit) must be zero
                assert(tx == 1'b0);
            end else if (f_sym_ctr == PORT_W + 2) begin
                // last symbol (stop bit) must be 1
                assert(tx == 1'b1);
            end else if (f_sym_ctr > 1 && f_sym_ctr < PORT_W + 2) begin
                // all other symbols should match the data to be transmitted, LSB first
                assert(tx == f_data_val[f_sym_ctr - 2]);
            end
        end
    `endif
endmodule
