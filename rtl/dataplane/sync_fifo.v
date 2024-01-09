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

/**
 * 2^N-1 Depth Synchronous FIFO
 *
 * This is a classic synchronous FIFO, with configurable data storage width and
 * depth. To prevent undefined behaviours on simultanious read/write events,
 * the FIFO is considered to be full when the write pointer is one storage
 * element away from the read pointer. This wastes on cell, and caps the storage
 * at 2^N - 1.
 *
 * To allow correct behaviour in synthesized hardware, data is only considered
 * "committed" and valid for future reads if it has been clocked in for one cycle.
 * Thus, simultanious read/writes are allowed when the FIFO is full, though simultanious
 * reads/writes when the FIFO is empty will lead to a succesful write and  unsuccessful
 * read since the data at element zero will not have been clocked in for 1 cycle at that
 * time. The data read in this case is considered to be undefined, and must not be used
 * by comsumers. Reads while the FIFO is empty with no accompanying write will set a
 * sticky underflow flag, and writes while the FIFO is full with no accompanying read
 * will set a sticky overflow flag. These error flags may be cleared by asserting the
 * reset signal. Reset will also empty the FIFO.
 *
 * A full proof targeted at the Symbiyosys toolchain has been included in this
 * design. See the formal verification block below for details on what areas of
 * the design are currently proven.
 *
 * Read/Write state summary table:
 * +------------------------------------------------------------------------+
 * | rd_en | wr_en | full | empty | read_ok | write_ok | overrun | underrun |
 * |==============================|=========================================|
 * |     0 |     0 |    x |     x |       0 |        0 |       0 |        0 |
 * |     0 |     1 |    0 |     x |       0 |        1 |       0 |        0 |
 * |     0 |     1 |    1 |     x |       0 |        0 |       1 |        0 |
 * |     1 |     0 |    x |     0 |       1 |        0 |       0 |        0 |
 * |     1 |     0 |    x |     1 |       0 |        0 |       0 |        1 |
 * |     1 |     1 |    0 |     x |       1 |        1 |       0 |        0 |
 * |     1 |     1 |    1 |     x |       1 |        1 |       0 |        0 |
 * |     1 |     1 |    x |     1 |       0 |        1 |       0 |        1 |
 * +------------------------------------------------------------------------+
 *
 * The wstatus siganl is packed as follows:
 *  - [1] -> will_fill
*   - [0] -> will_empty
 *
 * The status signal is packed as follows:
 *   - [1] -> full
 *   - [0] -> empty
 *
 * The error signal is packed as follows:
 *   - [1] -> underrun
 *   - [0] -> overrun
 */
module sync_fifo
#(
    parameter DATA_WIDTH = 8,
    parameter FIFO_SIZE = 511,
    parameter XRUN_MODE = "KEEP",
    localparam FIFO_IDX_W = $clog2(FIFO_SIZE)
) (
    input wire clk,
    input wire rst,
    input wire wr_en,
    input wire [DATA_WIDTH - 1:0] din,
    input wire rd_en,
    output wire [DATA_WIDTH - 1:0] dout,
    output wire [FIFO_IDX_W - 1:0] dcount,
    output wire [1:0] status,
    output wire [1:0] wstatus,
    output wire [1:0] error
);
    `include "util.vh"

    // validate params
    generate
        if (FIFO_SIZE <= 0 || !is_pow_2(FIFO_SIZE + 1)) begin : gen_validate_data_w
            $error("Parameter FIFO_SIZE must be 2^n - 1 && n > 0.", FIFO_SIZE);
        end
    endgenerate

    // one extra element to prevent the read pointer from ever being equal to the write
    // pointer in valid cases
    reg [DATA_WIDTH - 1:0] buffer [0:FIFO_SIZE];
    reg [FIFO_IDX_W - 1:0] wrptr = 'b0;
    reg [FIFO_IDX_W - 1:0] rdptr = 'b0;
    reg [FIFO_IDX_W - 1:0] data_count = 'b0;

    reg [DATA_WIDTH - 1:0] last_din = 0;
    reg [FIFO_IDX_W - 1:0] rdptr_nxt = 'b1;
    reg should_read_last_din = 0;
    reg may_fill = 0;
    reg may_empty = 0;

    reg full = 1'b0;
    reg empty = 1'b1;
    wire will_fill = may_fill && !rd_en && wr_en;
    wire will_empty = may_empty && rd_en && !wr_en;
    reg overrun = 1'b0;
    reg underrun = 1'b0;

    assign wstatus ={will_fill, will_empty};
    assign status = {full, empty};
    assign error = {overrun, underrun};
    assign dcount = data_count;

    wire rd_addr_en;
    wire wr_addr_en;
    generate
        if (XRUN_MODE == "KEEP") begin : uo_mode_stop
            assign wr_addr_en = wr_en && (!full || rd_en);
            assign rd_addr_en = rd_en && !empty;
        end else if (XRUN_MODE == "OVERWRITE") begin : uo_mode_continue
            // if full and writing but not reading, overwrite the oldest by advancing the read
            // pointer
            wire rd_skip = full && wr_en && !rd_en;
            assign wr_addr_en = wr_en;
            // if read while empty, output is always undefined
            assign rd_addr_en = (rd_en && !empty) || rd_skip;
        end else begin : uo_mode_invalid
            $error("Unsupported XRUN_MODE config.");
        end
    endgenerate

    reg [DATA_WIDTH - 1:0] dout_reg = 'b0;
    // break read and write up into two processes to encourage synthesis tooling to make
    // the correct inference choices
    wire [FIFO_IDX_W - 1:0] raddr = (!empty && rd_en)? rdptr_nxt : rdptr;
    always @(posedge clk) begin : wr_mem_access
        if (wr_addr_en)
            buffer[wrptr] <= din;
    end
    always @(posedge clk) begin : rd_mem_access
        dout_reg <= buffer[raddr];
    end
    assign dout = should_read_last_din? last_din : dout_reg;

    always @(posedge clk) begin : input_addr_gen
        if (rst) begin
            wrptr <= 'b0;
        end else if (wr_addr_en) begin
            wrptr <= wrptr + 1;
        end
    end

    always @(posedge clk) begin : output_addr_gen
        if (rst) begin
            rdptr <= 'b0;
            rdptr_nxt <= 'b1;
        end else if (rd_addr_en) begin
            rdptr <= rdptr + 1;
            rdptr_nxt <= rdptr_nxt + 1;
        end
    end

    always @(posedge clk) begin : under_over_run
        if (rst) begin
            overrun <= 1'b0;
            underrun <= 1'b0;
        end else begin
            // writes only over overflow if the will_overflow flag is set and there is no
            // corresponding read
            if (wr_en && full && !rd_en)
                overrun <= 1'b1;
            // reads always underflow if the will_underflow flag is set
            if (rd_en && empty)
                underrun <= 1'b1;
        end
    end

    always @(posedge clk) begin
        last_din <= din;
        should_read_last_din <= (empty && wr_addr_en);
    end

    // generate control signals using registered logic to reduce logic fanout on datapath
    // nets
    always @(posedge clk) begin : update_status
        if (rst) begin
            data_count <= 'b0;
            full <= 1'b0;
            empty <= 1'b1;
            may_fill <= 1'b0;
            may_empty <= 1'b0;
        end else begin
            // calcualte value for status components
            casez({wr_en, rd_en, full, empty})
                4'b01?0: begin
                    data_count <= data_count - 1;
                    full <= 1'b0;
                    empty <= data_count == 1;
                    may_empty <= data_count == 2;
                    may_fill <= data_count == FIFO_SIZE;
                end
                // write with no read, or successful write, but failed read since fifo is empty.
                // In either case, the fifo is not empty any more.
                4'b100?, 4'b1101: begin
                    data_count <= data_count + 1;
                    empty  <= 1'b0;
                    full <= data_count == FIFO_SIZE - 1;
                    may_fill <= data_count == FIFO_SIZE - 2;
                    may_empty <= data_count == 0;
                end
                // 4'b111? does not overflow, but the amount of data does
                // not change (successful read and write while the fifo is close to overflowing)
                // for all other cases, rd_en && wr_en or !rd_en && !rd_en so the amount of data
                // will not change, nor will full/empty status
                default: begin
                    data_count <= data_count;
                    full <= full;
                    empty <= empty;
                    may_fill <= may_fill;
                    may_empty <= may_empty;
                end
            endcase
        end
    end

    ///////////////////////////////////////////////////////////////////////////
    ///////////////////////////////////////////////////////////////////////////
    // Formal verification logic
    //
    // Verifies the following properties:
    // - In general, writes are considered to be "committed" if they have been
    //   held for one cycle.
    // - Read/Write interactions:
    //   - Read while not empty succeeds
    //   - Write while not full succeeds.
    //   - Simultanious read/write while full succeeds.
    //   - Simulatnious read/write while emty leads to successful write,
    //     failed read. The data read is undefined and must not be used.
    //   - Read-only while empty underflow and sets a sticky error flag.
    //   - Write-only while full overflows and sets a sticky error flag.
    //     - If the overrun mode is set to CONTINUOUS, the oldest data
    //       element is overwritten and the read pointer is updated
    //       accordingly.
    // - The count of data elements in the fifo is correct at all times.
    // - Full and Empty are correct at all times
    // - Reset makes it look like the FIFO has been emptied by reseting the
    //   data counter and pointer.
    // - TODO: datapath validation.
    ///////////////////////////////////////////////////////////////////////////
    ///////////////////////////////////////////////////////////////////////////
    `ifdef FORMAL
        `ifdef SYNC_FIFO
            `define ASSUME assume
        `else
            `define ASSUME assert
        `endif
        /////////////////////////////////////////////////////////
        // Observers and utility signals
        /////////////////////////////////////////////////////////
        reg f_past_valid = 1'b0;
        integer f_trace_cycles = 0;
        always @(posedge clk) begin
            f_past_valid <= 1'b1;
            f_trace_cycles <= f_trace_cycles + 1;
        end

        localparam [FIFO_IDX_W - 1:0] F_PTR_MAX_VAL = {(FIFO_IDX_W){1'b1}};

        wire f_overrun_cond = wr_en && full && !rd_en;
        wire f_underrun_cond = rd_en && empty;
        wire [FIFO_IDX_W - 1:0] f_expected_dcount = wrptr - rdptr;
        wire f_rd_skip = XRUN_MODE == "OVERWRITE" && wr_en && !rd_en && full;

        reg f_rst_reg = 1'b0;
        always @(posedge clk)
            f_rst_reg <= rst;

        // force cover to actually start the fifo with non-matching data
        `ifdef COVER
            genvar f_cov_i;
            generate
                for (f_cov_i = 0; f_cov_i <= FIFO_SIZE; f_cov_i = f_cov_i + 1) begin
                    restrict property(f_past_valid || buffer[f_cov_i] == 'b0);
                end
            endgenerate
        `endif
        /////////////////////////////////////////////////////////
        // Property Specification (contract)
        /////////////////////////////////////////////////////////
        always @(posedge clk) begin : f_cover_props
            `ifdef COVER
                    // make cover data more interesting than just a stream of zeroes to
                    // aid visual inspection
                    assume(f_trace_cycles <= 2 || (din != $past(din, 1) && din != $past(din, 2)));
            `endif
            can_fill: cover(full);
            can_empty: cover(empty);
            can_overfill: cover(overrun && full);
            can_empty_after_overfill: cover(overrun && empty);
            can_underrun: cover(underrun && empty);
            can_underrun_after_filling: cover(underrun && full);
        end

        always @(*) begin : f_props_always_true
            data_count_correct: assert(data_count == f_expected_dcount);
            // only allow a read-write conflict during an empty-underrun as the data is
            // undefined anyways. All other cases must have different pointers for the
            // read and write to be valid, as simultanious read/write to the same address
            // is only guranteed to carry out the write in most FPGA architectures.
            if (!rst && rd_en && wr_en && !empty)
                no_rw_conflict: assert(wrptr != rdptr);
        end

        always @(posedge clk) begin : f_ptr_props
            if (!f_rst_reg) begin
                if (f_past_valid) begin
                    // monotonicity property of both pointers
                    wrptr_monotonic: assert($stable(wrptr) ||
                                            wrptr == $past(wrptr) + 1 ||
                                            (wrptr == 0 && $past(wrptr) == F_PTR_MAX_VAL));
                    rdptr_monotonic: assert($stable(rdptr) ||
                                            rdptr == $past(rdptr) + 1 ||
                                            (rdptr == 0 && $past(rdptr) == F_PTR_MAX_VAL));
                    // data count must either stay stable or increment or decrement by one
                    data_count_delta: assert($stable(data_count) ||
                                             data_count == $past(data_count) + 1 ||
                                             data_count == $past(data_count) - 1);
                    // change can only occur if the corresponding enable was high
                    wrptr_chg_if_wren: assert(!$changed(wrptr) || $past(wr_en));
                    rdptr_chg_if_rden: assert(!$changed(rdptr) || $past(rd_en) || $past(f_rd_skip));
                    rdptr_nxt_v: assert(rdptr_nxt == rdptr + 1 ||
                                        (rdptr == F_PTR_MAX_VAL && rdptr_nxt == 0));
               end
            end else begin // rst is high
                rst_wrptr:  assert(wrptr == 0);
                rst_rdptr:  assert(rdptr == 0);
                rst_dcount: assert(data_count == 0);
            end
        end

        always @(posedge clk) begin : f_full_empty_props
            // it should never should be true that the will_overflow and will_underflow are
            // true at the same time
            not_empty_and_full: assert(!(empty && full));
            if (!f_rst_reg) begin
                // full and empty are correct
                afull: assert(!full || data_count == FIFO_SIZE);
                nfull: assert(full || data_count != FIFO_SIZE);
                aempty: assert(!empty || data_count == 0);
                nempty: assert(empty || data_count != 0);
                fullptr_1gap: assert(!full ||
                                     wrptr + 1 == rdptr ||
                                     (wrptr ==  F_PTR_MAX_VAL && rdptr == 0));
                awill_fill: assert(!will_fill || (data_count == FIFO_SIZE - 1 && wr_en && !rd_en));
                nwill_fill: assert(will_fill || !(data_count == FIFO_SIZE - 1 && wr_en && !rd_en));
                awill_empty: assert(!will_empty || (data_count == 1 && !wr_en && rd_en));
                nwill_empty: assert(will_empty || !(data_count == 1 && !wr_en && rd_en));
                may_fill_v: assert(!may_fill || data_count == FIFO_SIZE - 1);
                may_fill_n: assert(may_fill || data_count != FIFO_SIZE - 1);
                may_empty_v: assert(!may_empty || data_count == 1);
                may_empty_n: assert(may_empty || data_count != 1);
            end else begin
                rst_full:  assert(!full);
                rst_empty: assert(empty);
            end
        end

        always @(posedge clk) begin : f_under_over_flow_ptr_props
            if (!f_rst_reg && f_past_valid) begin
                if (XRUN_MODE == "KEEP") begin
                    // no changes on overrun condition
                    orun_nchng: assert(!$past(f_overrun_cond) ||
                                       (wrptr == $past(wrptr) && rdptr == $past(rdptr)));
                end else if (XRUN_MODE == "OVERWRITE") begin
                    // oldest data element got overwritten
                    orun_owr: assert(!$past(f_overrun_cond) ||
                                     ((wrptr == $past(wrptr) + 1 ||
                                       wrptr == 0 && $past(wrptr) == F_PTR_MAX_VAL) &&
                                      (rdptr == $past(rdptr) + 1 ||
                                       rdptr == 0 && $past(rdptr) == F_PTR_MAX_VAL)));
                end
                urun_nchng: assert(!$past(f_underrun_cond) || (rdptr == $past(rdptr)));
            end
        end

        always @(posedge clk) begin : f_under_over_flow_props
            if (!f_rst_reg) begin
                if (f_past_valid) begin
                    // over/under run flag should be sticky until reset
                    overrun_sticky: assert(!$past(overrun) || overrun);
                    underrun_sticky: assert(!$past(underrun) || underrun);
                    // various props of read/write full/empty
                    casez({$past(wr_en), $past(rd_en), $past(full), $past(empty)})
                        4'b1110: rw_full_no_xrun: assert(!$rose(overrun) && $stable(data_count));
                        4'b1010: w_full_overrun: assert(overrun && $stable(data_count));
                        4'b1101: rw_empty_underrun: assert(underrun && data_count == $past(data_count) + 1);
                        4'b0101: r_empty_underrun: assert(underrun && $stable(data_count));
                    endcase
                end
            end else begin
                rst_orun: assert(!overrun);
                rst_urun: assert(!underrun);
            end
        end
    `endif
endmodule
