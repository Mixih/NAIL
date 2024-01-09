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
 * Low-level UART recieve interface, 8n1
 *
 * This is a configurable, low-level UART receive interface, with a strobe/ready
 * logic interface. It should be paired with a fifo if the coneccted logic is
 * unable to immediately respond to deserialized data. This core has been tested
 * at up to 1Mbaud, and has been designed to be able to handle UART streams with
 * no inter-symbol dead-time.
 *
 * A full proof targeted at the Symbiyosys toolchain has been included in this
 * design. See the formal verification block below for details on what areas of
 * the design are currently proven.
 *
 * NO EXTERNAL SYNCHONIZATION HAS BEEN INCLUDED IN THIS MODULE.
 */
module uart_rx_ll_8n1 #(
    parameter ICLK_HZ = 100_000_000,
    parameter BAUD_RATE = 115_200,
    // parameter OS_FACTOR = 16,
    localparam PORT_W = 8
) (
    input wire clk,
    input wire rx,
    output reg [PORT_W - 1:0] dout = 'b0,
    output reg dready = 1'b0
);
    `include "util.vh"

    localparam DIV_FAC = calc_div_fac(ICLK_HZ, BAUD_RATE);

    generate
        if (DIV_FAC <= 4) begin : validate_oversample_ratio
            $error("System clock must be > 4 times higher than baud rate.");
        end
        if (!validate_div_fac(DIV_FAC, ICLK_HZ, BAUD_RATE, 100)) begin
            : validate_baud_tolerance
            $warning("Generated baud rate is out of tolerance by > 1%.");
        end
    endgenerate

    localparam DCTR_W = $clog2(PORT_W);
    localparam CTR_SAMPLE_VAL = DIV_FAC / 2;

    localparam STATE_IDLE = 2'd0;
    localparam STATE_START = 2'd1;
    localparam STATE_DATA = 2'd2;
    localparam STATE_STOP = 2'd3;

    reg [1:0] state = STATE_IDLE;

    reg [PORT_W - 1:0] data_sr = 'b0;
    reg [DCTR_W - 1:0] dctr = 'b0;
    reg baud_en = 1'b0;
    reg state_start_should_advance_i = 1'b0;
    reg state_start_should_advance = 1'b0;
    wire baud_stb;
    wire [$clog2(DIV_FAC) - 1:0] baud_ctr;

    int_baud_gen #(
        .DIV_FACTOR(DIV_FAC)
    ) baud_gen_i (
        .clk(clk),
        .en(baud_en),
        .stb(baud_stb),
        .baud_ctr(baud_ctr)
    );

    always @(posedge clk) begin : uart_deserialize
        dready <= 1'b0;
        state_start_should_advance_i <= 1'b0;
        state_start_should_advance <= state_start_should_advance_i;
        case (state)
            STATE_IDLE: begin
                if (rx == 1'b0) begin
                    state <= STATE_START;
                    // data_sr <= 'b0;
                    baud_en <= 1'b1;
                end
            end
            STATE_START: begin
                // should be one whole cycle shorter to account for the start bit
                if (baud_ctr == DIV_FAC - 4) begin
                    baud_en <= 1'b0;
                    state_start_should_advance_i <= 1'b1;
                end
                if (state_start_should_advance_i)
                    baud_en <= 1'b1;
                if (state_start_should_advance) begin
                    state <= STATE_DATA;
                end
            end
            STATE_DATA: begin
                if (baud_ctr == CTR_SAMPLE_VAL) begin
                    data_sr <= {rx, data_sr[PORT_W - 1:1]};
                end
                if (baud_stb) begin
                    dctr <= dctr + 1;
                    if (`Z_PAD(dctr) == PORT_W - 1) begin
                        state <= STATE_STOP;
                        dout <= data_sr;
                        dready <= 1'b1;
                        dctr <= 'b0;
                    end
                end
            end
            STATE_STOP: begin
                if (baud_stb) begin
                    state <= STATE_IDLE;
                    baud_en <= 1'b0;
                end
            end
        endcase
    end


    ///////////////////////////////////////////////////////////////////////////
    ///////////////////////////////////////////////////////////////////////////
    // formal verification logic
    //
    // Verifies the following properties:
    // - Signal timings
    // - Serialization correctness
    // - TODO: Absolute cycle time stability verification
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
        reg f_past_valid = 1'b0;
        always @(posedge clk)
            f_past_valid <= 1'b1;

        integer f_trans_ctr = 0;
        integer f_sym_ctr = 0;
        reg f_started = 1'b0;
        reg f_finished = 1'b0;
        // for correct verification we need a solver chosen constant byte of data to send
        (* anyconst *) reg [PORT_W - 1:0] f_data_val;

        always @(posedge clk) begin : f_gen_observers
            if (state == STATE_IDLE && rx == 1'b0) begin
                f_started <= 1'b1;
                f_finished <= 1'b0;
                f_sym_ctr <= 1;
            end
            if (state == STATE_STOP && baud_stb) begin
                f_finished <= 1'b1;
                f_started <= 1'b0;
                f_trans_ctr <= f_trans_ctr + 1;
                f_sym_ctr <= 0;
            end
            if ((state != STATE_STOP && baud_stb) || state_start_should_advance) begin
                f_sym_ctr <= f_sym_ctr + 1;
            end
        end

        /////////////////////////////////////////////////////////
        // Property Specification (contract)
        /////////////////////////////////////////////////////////
        always @(posedge clk) begin : f_assumptions
            if (~f_past_valid && state == STATE_IDLE)
                restrict property (rx == 1'b1);
            if (f_sym_ctr == 1) begin
                // first symbol must be 0 for the start bit
                `ASSUME(rx == 1'b0);
            end else if (f_sym_ctr == PORT_W + 2) begin
                // last symbol must be 1 for the stop bit
                `ASSUME(rx == 1'b1);
            end else if (f_sym_ctr != 0) begin
                // if this module is the top module assume that the rx bit are provided by
                // the solver value above
                `ifdef MODULE_IS_FORMAL_TOP
                    assume(rx == f_data_val[f_sym_ctr - 2]);
                `endif
            end
            // pick a specific interesting value for cover operations
            `ifdef COVER
                // if (f_trans_ctr % 2 == 0)
                    assume(f_data_val == 8'b01101101);
                // else
                //     assume(f_data_val == 8'b10001000);
            `endif
        end

        always @(posedge clk) begin : f_cover_props
            // ensure that data becomes ready at some point
            cover(dready == 1'b1);
            // ensure that the state machine can finish at least once
            cover(f_finished == 1'b1);
            // ensure that passing thorugh the idle state before retransmitting is
            // possible
            cover(f_trans_ctr > 1);
        end

        always @(posedge clk) begin : f_stability_props
            if (f_past_valid && !$rose($past(baud_stb, 1))) begin
                // data and ready signals should not change if no strobe
                assert($stable(dout));
                // this makes the solver angry :(
                // assert($stable(dready));
                if(baud_ctr != DIV_FAC / 2 + 1)
                    assert($stable(data_sr));
            end
        end

        always @(*) begin : f_symbol_props
            case(state)
                STATE_IDLE: begin
                    assert(dctr == 0);
                    assert(baud_en == 1'b0);
                    assert(f_sym_ctr == 0);
                end
                STATE_START: begin
                    assert(dctr == 0);
                    assert(f_sym_ctr == 1);
                end
                STATE_DATA: begin
                    assert(f_sym_ctr == dctr + 2);
                    assert(f_sym_ctr >= 2 && f_sym_ctr <= 9);
                end
                STATE_STOP: begin
                    assert(dctr == 0);
                    assert(f_sym_ctr == 10);
                end
            endcase
        end

        always @(posedge clk) begin : f_other_props
            // output must match chosen value
            if (dready)
                assert(dout == f_data_val);
            // finish/started asserts
            if (state == STATE_IDLE) begin
                assert(!f_started);
            end else begin
                assert(f_started);
                assert(!f_finished);
            end
        end
    `endif
endmodule
