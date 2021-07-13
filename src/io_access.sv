//=======================================================================
// Created by         : KU Leuven
// Filename           : io_access.sv
// Author             : Nimish Shah
// Created On         : 2020-01-08 20:05
// Last Modified      : 
// Update Count       : 2020-01-08 20:05
// Description        : 
//                      
//=======================================================================

`ifndef IO_ACCESS_DEF
  `define IO_ACCESS_DEF

  `include "common.sv"
  
module io_mem_access (
  input clk,
  input rst,

  input [periphery_pkg::INPUT_REG_L - 1 : 0] in,

  input wr_en,
  input rd_en,

  // global
  output [GLOBAL_MEM_ADDR_L - 1 : 0]  init_global_mem_addr,
  output                              init_global_mem_vld,
  output                              init_global_mem_wr_en,
  output [DATA_L - 1 : 0]             init_global_mem_wr_data,
  input [DATA_L - 1 : 0]            init_global_mem_rd_data,
  input                             init_global_mem_rd_data_vld,

  // local
  output  [LOCAL_MEM_ADDR_L - 1 : 0]  init_local_mem_addr,
  output  [N_PE - 1 : 0]              init_local_mem_vld,
  output  [N_PE - 1 : 0]              init_local_mem_wr_en,
  output  [DATA_L - 1 : 0]            init_local_mem_wr_data,
  input [N_PE - 1 : 0] [DATA_L - 1 : 0] init_local_mem_rd_data,
  input [N_PE - 1 : 0]                  init_local_mem_rd_data_vld,

  // stream
  output [DATA_L - 1 : 0]                                         init_stream_wr_data,
  output [$clog2(N_PE) +stream_pkg::INSTR_STR_ADDR_L + 2 - 1 : 0] init_stream_addr,
  output                                                          init_stream_wr_vld,
  output                                                          init_stream_rd_vld,
  input [DATA_L - 1 : 0]                                          init_stream_rd_data,
  input                                                           init_stream_rd_data_vld,

  output [periphery_pkg::OUTPUT_DATA_L -1 : 0] out
); 
  import periphery_pkg::*;

  logic [DATA_L - 1 : 0] in_data;
  logic [DATA_L - 1 : 0] in_addr;

  assign in_data = in[0 +: DATA_L];
  assign in_addr = in[DATA_L +: DATA_L];

  logic [periphery_pkg::OUTPUT_DATA_L - 1 : 0] out_pre;


  logic is_global;
  logic is_local;
  logic is_stream;
  
  logic [$clog2(N_PE) - 1 : 0] local_bank_id;
  logic  [N_PE - 1 : 0]              init_local_mem_vld_pre;
  logic  [N_PE - 1 : 0]              init_local_mem_wr_en_pre;
  
  assign local_bank_id = in_addr[LOCAL_MEM_ADDR_L +: $bits(local_bank_id)];

  assign is_global = (in_addr[$bits(in_addr) - 1 -: ADDR_TYPE_L] == ADDR_TYPE_GLOBAL) ? 1'b1: 1'b0;
  assign is_local  = (in_addr[$bits(in_addr) - 1 -: ADDR_TYPE_L] == ADDR_TYPE_LOCAL) ? 1'b1: 1'b0;
  assign is_stream = (in_addr[$bits(in_addr) - 1 -: ADDR_TYPE_L] == ADDR_TYPE_STREAM) ? 1'b1: 1'b0;

  always_comb begin
    out_pre= init_global_mem_rd_data;

    foreach ( init_local_mem_rd_data_vld[i]) begin
      if (init_local_mem_rd_data_vld[i] == 1) begin
        out_pre= init_local_mem_rd_data[i];
      end
    end

    if (init_global_mem_rd_data_vld) begin
      out_pre= init_global_mem_rd_data;
    end

    if (init_stream_rd_data_vld) begin
      out_pre= init_stream_rd_data;
    end
  end

  always_comb begin
    init_local_mem_vld_pre= '0;
    init_local_mem_wr_en_pre= '0;
    
    init_local_mem_wr_en_pre[local_bank_id] = is_local ? wr_en : 1'b0;
    init_local_mem_vld_pre[local_bank_id] = is_local ? (wr_en | rd_en) : 1'b0;
  end


  assign init_global_mem_wr_data = in_data;
  assign init_local_mem_wr_data = in_data;

  assign init_global_mem_addr = in_addr;
  assign init_local_mem_addr = in_addr;
  
  assign out = out_pre;

  assign init_global_mem_wr_en = is_global ? wr_en : 1'b0;
  assign init_global_mem_vld = is_global ? (wr_en | rd_en) : 1'b0;

  assign init_local_mem_vld = init_local_mem_vld_pre;
  assign init_local_mem_wr_en = init_local_mem_wr_en_pre;

  assign init_stream_wr_data= in_data;
  assign init_stream_addr= in_addr;
  assign init_stream_wr_vld= is_stream ? wr_en : 1'b0;

  assign init_stream_rd_vld= is_stream ? rd_en : 1'b0;


endmodule

`endif //IO_ACCESS_DEF
