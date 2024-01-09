/*
 * SPDX-FileCopyrightText:  Copyright (C) 2023, Max Hahn
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

module argmax #(
    parameter PORT_W = 8,
    parameter INPUT_ELTS = 10,
    parameter ADDR_DATA_DELAY = 2,
    localparam IADDR_W = $clog2(INPUT_ELTS)
) (
    input wire clk,
    input wire start,
    output reg done = 0,
    output reg [IADDR_W - 1:0] addri = 0,
    input wire signed [PORT_W - 1:0] din,
    output reg [IADDR_W - 1:0] maxidx = 0
);
    `include "util.vh"

    localparam [PORT_W - 1:0] INT_MIN = {1'b1, {(PORT_W - 1){1'b0}}};

    localparam STATE_IDLE = 3'd0;
    localparam STATE_STARTING_UP = 3'd1;
    localparam STATE_PUMP_PIPELINE = 3'd2;
    localparam STATE_BUSY = 3'd3;
    localparam STATE_FLUSH_PIPELINE = 3'd4;

    reg [2:0] state = STATE_IDLE;

    wire state_busy_should_advance;
    wire delay_next;
    wire [IADDR_W - 1:0] addri_next;
    reg [ADDR_DATA_DELAY - 1:0] delay_sr = 'b0;
    wire [IADDR_W - 1:0] addri_delay_next;
    reg [ADDR_DATA_DELAY * IADDR_W - 1:0] addri_delay_sr = 'b0;

    reg signed [PORT_W - 1:0] maxval = INT_MIN;

    assign state_busy_should_advance = addri == INPUT_ELTS - 1;
    assign delay_next = state == STATE_STARTING_UP || state_busy_should_advance;
    assign addri_next = (!state_busy_should_advance
                         && (state == STATE_PUMP_PIPELINE || state == STATE_BUSY))?
                        addri + 1 : 0;
    assign addri_delay_next = addri;

    always @(posedge clk) begin : argmax_proc
        // do argmax
        if (state == STATE_BUSY || state == STATE_FLUSH_PIPELINE) begin
            if (din > maxval) begin
                maxval <= din;
                maxidx <= addri_delay_sr[`SLICE(ADDR_DATA_DELAY - 1, IADDR_W)];
            end
        end else if (state == STATE_IDLE) begin
            maxval <= INT_MIN;
            maxidx <= 0;
        end
    end

    always @(posedge clk) begin : state_machine
        case (state)
            STATE_IDLE: begin
                done <= 1'b0;
                if (start) begin
                    state <= STATE_STARTING_UP;
                end
            end
            STATE_STARTING_UP: begin
                state <= STATE_PUMP_PIPELINE;
            end
            STATE_PUMP_PIPELINE: begin
                if (delay_sr[ADDR_DATA_DELAY - 1]) begin
                    state <= STATE_BUSY;
                end
            end
            STATE_BUSY: begin
                if (state_busy_should_advance) begin
                    state <= STATE_FLUSH_PIPELINE;
                end
            end
            STATE_FLUSH_PIPELINE: begin
                if (delay_sr[ADDR_DATA_DELAY - 1]) begin
                    done <= 1'b1;
                    state <= STATE_IDLE;
                end
            end
            default: begin
                done <= 1'bx;
                state <= 3'bx;
            end
        endcase
    end

    always @(posedge clk) begin : shift_reg_proc
        addri <= addri_next;
        delay_sr <= {delay_sr[ADDR_DATA_DELAY - 2:0], delay_next};
        addri_delay_sr <= {addri_delay_sr[`SLICE_R(ADDR_DATA_DELAY - 2, 0, IADDR_W)], addri_delay_next};
    end

    ///////////////////////////////////////////////////////////////////////////
    ///////////////////////////////////////////////////////////////////////////
    // Formal verification block
    //
    // Verifies the following properties:
    // - Design can proceed through full state machine until the done signal
    //   is raised (cover)
    // - Design fulfills the argmax() contract (the index of the maximum
    //   item encountered. In the case of the multiple instances of the max
    //   value, the lowest address shall be returned.
    // - done is asserted at the end of the computation, and is only ever high
    //   for one clock cycle
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

        reg f_started = 'b0;
        reg f_finished = 'b0;
        integer f_processed_ctr = 'b0;
        integer f_ctr = 'b0;

        always @(posedge clk) begin : calc_observers
            if (start && state == STATE_IDLE) begin
                f_started <= 1'b1;
                f_finished <= 1'b0;
                f_ctr <= 'b0;
            end else if (done) begin
                f_processed_ctr <= f_processed_ctr + 1;
                f_started <= 1'b0;
                f_finished <= 1'b1;
            end else if (f_started) begin
                f_ctr <= f_ctr + 1;
            end
        end

        /////////////////////////////////////////////////////////
        // Correctness input gen
        /////////////////////////////////////////////////////////
        // solver chooses the max index and the max value and holds it constant across the
        // current basecase check (but allows it to vary to any possible value between
        // individual cases)
        (* anyconst *) reg signed [PORT_W - 1:0] f_dmax;
        (* anyconst *) reg [IADDR_W - 1:0] f_maxi;
        reg signed [PORT_W - 1:0] f_din_arr [0:INPUT_ELTS - 1];
        reg [PORT_W * ADDR_DATA_DELAY - 1:0] f_din_sr = 'b0;
        // the top of the shift register that is ADDR_DATA_DELAY cycles behind
        wire signed [PORT_W - 1:0] f_din = f_din_sr[`SLICE(ADDR_DATA_DELAY - 1, PORT_W)];

        always @(*) begin : fdin_assumption_props
            // for verification purposes, assume that the data input is always the
            // array built by the solver
            assume(din == f_din);
            assume(f_maxi >= 0 && f_maxi < INPUT_ELTS);
        end

        always @(posedge clk) begin : f_din_signal_gen
            // simulate the input delay between teh address and data presentation
            f_din_sr <= {f_din_sr[`SLICE_R(ADDR_DATA_DELAY - 2, 0, PORT_W)], f_din_arr[addri]};
        end

        genvar f_din_i;
        generate
            for (f_din_i = 0; f_din_i < INPUT_ELTS; f_din_i = f_din_i + 1) begin : f_gen_inputs
                // allow any memory value other than the max value to vary on
                // each cycle, so long as the value never exceends the max value
                (* anyseq *) reg signed [PORT_W - 1:0] f_dvali;
                always @(*) begin
                    if (f_din_i == f_maxi) begin
                        assume(f_dvali == f_dmax);
                    end else if (f_din_i > f_maxi) begin
                        assume(f_dvali <= f_dmax);
                    end else begin // f_din_i < f_maxi
                        assume(f_dvali < f_dmax);
                    end
                    f_din_arr[f_din_i] = f_dvali;
                end
            end
        endgenerate

        /////////////////////////////////////////////////////////
        // Property Specification (contract)
        /////////////////////////////////////////////////////////
        always @(posedge clk) begin : f_cover_props
            cover(done == 1'b1);                      // finishes processing
            cover(f_processed_ctr == 4);              // can process four items consecutively
            cover(done == 1'b1 && f_dmax == INT_MIN); // finishes when maxval is limit_min<INT>
        end

        always @(posedge clk) begin : formal_prop_true_on_edge
            if (f_started) begin
                // ensure that every possible input array will complete in at least
                // 2 * ADDR_DATA_DELAY + INPUT_ELTS + 1 cycles
                if (f_ctr > 2 * ADDR_DATA_DELAY + INPUT_ELTS + 1) begin
                    assert(f_finished);
                end
                if (done) begin
                    // output must be in range of possible input addresses
                    assert(maxidx < INPUT_ELTS);
                    // output should match constructed output
                    assert(maxidx == f_maxi);
                end
            end
            // done must only be high for one cycle
            if (f_past_valid)
                assert((done && done != $past(done, 1)) || ~done);
        end

        always @(*) begin : formal_props_always_true
            // state must not be idle if started
            if (f_started && !done)
                assert(state != STATE_IDLE);
            // state must be idle if finished
            if (f_finished)
                assert(state == STATE_IDLE);
            // if in pipeline start/flush stages, the delay shift register must contain
            // exactly one '1' value
            if (state == STATE_PUMP_PIPELINE || state == STATE_FLUSH_PIPELINE)
                assert($countones(delay_sr) == 1);
            // ensure the state value never goes out of range
            assert(state <= STATE_FLUSH_PIPELINE);
            // generated address must be valid
            assert(addri < INPUT_ELTS);
        end
    `endif
endmodule
