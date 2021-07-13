//=======================================================================
// Created by         : KU Leuven
// Filename           : io_monitor.sv
// Author             : Nimish Shah
// Created On         : 2020-02-26 21:10
// Last Modified      : 
// Update Count       : 2020-02-26 21:10
// Description        : 
//                      
//=======================================================================

`ifndef IO_MONITOR_DEF
  `define IO_MONITOR_DEF

module io_monitor (
  input [periphery_pkg::INPUT_REG_L - 1 : 0] reg_data,
  
  input [N_PE - 1 : 0] global_rd_req,
  input [N_PE - 1 : 0] global_rd_gnt,
  input [N_PE - 1 : 0] global_wr_req,
  input [N_PE - 1 : 0] global_wr_gnt,

  input [N_PE - 1 : 0] instr_stream_req,
  input [N_PE - 1 : 0] instr_stream_gnt,
  input [N_PE - 1 : 0] ld_stream_req,
  input [N_PE - 1 : 0] ld_stream_gnt,
  input [N_PE - 1 : 0] st_stream_req,
  input [N_PE - 1 : 0] st_stream_gnt,

  input [N_PE - 1 : 0] [DATA_L - 1 : 0] pe_out,
  input [N_PE - 1 : 0] [INSTR_L - 1 : 0] instr,
  output [DATA_L - 1 : 0] out
); 
  import periphery_pkg::*;

  logic [DATA_L - 1 : 0] out_pre;
  
  logic [MONITOR_OPCODE_L - 1 : 0] monitor_opcode;
  assign monitor_opcode = reg_data [0 +: MONITOR_OPCODE_L];

  always_comb begin
    out_pre = global_rd_req [0 +: DATA_L];

`ifndef DESIGN_EXPLORE
    case (monitor_opcode) 
      MONITOR_OPCODE_NOP : out_pre = 0;
      MONITOR_OPCODE_GLOBAL_RD_REQ_0 : out_pre = global_rd_req[0 +: DATA_L]; 
      MONITOR_OPCODE_GLOBAL_RD_REQ_1 : out_pre = global_rd_req[DATA_L +: DATA_L];
      MONITOR_OPCODE_GLOBAL_WR_REQ_0 : out_pre = global_wr_req[0 +: DATA_L];
      MONITOR_OPCODE_GLOBAL_WR_REQ_1 : out_pre = global_wr_req[DATA_L +: DATA_L];
      MONITOR_OPCODE_GLOBAL_RD_GNT_0 : out_pre = global_rd_gnt[0 +: DATA_L];
      MONITOR_OPCODE_GLOBAL_RD_GNT_1 : out_pre = global_rd_gnt[DATA_L +: DATA_L];
      MONITOR_OPCODE_GLOBAL_WR_GNT_0 : out_pre = global_wr_gnt[0 +: DATA_L];
      MONITOR_OPCODE_GLOBAL_WR_GNT_1 : out_pre = global_wr_gnt[DATA_L +: DATA_L];

      MONITOR_OPCODE_INSTR_STREAM_REQ_0: out_pre = instr_stream_req[0 +: DATA_L];
      MONITOR_OPCODE_INSTR_STREAM_REQ_1: out_pre = instr_stream_req[DATA_L +: DATA_L];
      MONITOR_OPCODE_LD_STREAM_REQ_0   : out_pre = ld_stream_req   [0 +: DATA_L];
      MONITOR_OPCODE_LD_STREAM_REQ_1   : out_pre = ld_stream_req   [DATA_L +: DATA_L];
      MONITOR_OPCODE_ST_STREAM_REQ_0   : out_pre = st_stream_req   [0 +: DATA_L];
      MONITOR_OPCODE_ST_STREAM_REQ_1   : out_pre = st_stream_req   [DATA_L +: DATA_L];
      MONITOR_OPCODE_INSTR_STREAM_GNT_0: out_pre = instr_stream_gnt[0 +: DATA_L];
      MONITOR_OPCODE_INSTR_STREAM_GNT_1: out_pre = instr_stream_gnt[DATA_L +: DATA_L];
      MONITOR_OPCODE_LD_STREAM_GNT_0   : out_pre = ld_stream_gnt   [0 +: DATA_L];
      MONITOR_OPCODE_LD_STREAM_GNT_1   : out_pre = ld_stream_gnt   [DATA_L +: DATA_L];
      MONITOR_OPCODE_ST_STREAM_GNT_0   : out_pre = st_stream_gnt   [0 +: DATA_L];
      MONITOR_OPCODE_ST_STREAM_GNT_1   : out_pre = st_stream_gnt   [DATA_L +: DATA_L];

      MONITOR_OPCODE_POSIT_OUT : out_pre = pe_out[reg_data[MONITOR_OPCODE_L +: $clog2(N_PE)]];
      MONITOR_OPCODE_INSTR : out_pre = instr[reg_data[MONITOR_OPCODE_L +: $clog2(N_PE)]];

      default : out_pre = global_rd_req[0 +: DATA_L];
    endcase
`endif
  end

  assign out = out_pre; 
endmodule



`endif //IO_MONITOR_DEF
