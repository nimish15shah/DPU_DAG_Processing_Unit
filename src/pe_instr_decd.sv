//=======================================================================
// Created by         : KU Leuven
// Filename           : pe_instr_decd.sv
// Author             : Nimish Shah
// Created On         : 2019-12-06 16:08
// Last Modified      : 
// Update Count       : 2019-12-06 16:08
// Description        : 
//                      
//=======================================================================
`ifndef PE_INSTR_DECD_DEF
  `define PE_INSTR_DECD_DEF

`include "common.sv"

module pe_instr_decd (
   input [INSTR_L - 1 : 0]     instr,

   output [OPCODE_L - 1: 0]    opcode,
   output [REG_ADDR_L - 1 : 0] reg_rd_addr_0,
   output [REG_ADDR_L - 1 : 0] reg_rd_addr_1,
   output [REG_ADDR_L - 1 : 0] operator_reg_wr_addr,

   output                      ld_0_en,
   output                      ld_1_en,
   output                      st_en,
    
   output [pe_pkg::LD_STREAM_CNT_L - 1 : 0] ld_stream_len

); 
  import pe_pkg::*;
  
  assign opcode = instr[OPCODE_L - 1 : 0];
  
  assign reg_rd_addr_0 = instr[INPUT_REG_0_S +: INPUT_REG_0_L]; // equivalent to instr[INPUT_REG_0_S + INPUT_REG_0_L - 1 : INPUT_REG_0_S]
  assign reg_rd_addr_1 = instr[INPUT_REG_1_S +: INPUT_REG_1_L];
  assign operator_reg_wr_addr = instr[OUTPUT_REG_S +: OUTPUT_REG_L];
  
  assign ld_0_en = instr[LD_0_EN_S +: 1];
  assign ld_1_en = instr[LD_1_EN_S +: 1];
  assign st_en= instr[ST_EN_S +: 1];
  
  assign ld_stream_len = instr[SET_LD_STREAM_LEN_S +: SET_LD_STREAM_LEN_L];
endmodule

`endif //PE_INSTR_DECD_DEF
