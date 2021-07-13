
`ifndef COMMON_DEF
  `define COMMON_DEF

`define DESIGN_EXPLORE

`ifndef VERIFICATION
  `define USE_SRAM_MACRO
`endif

`ifdef VERIFICATION
  `define VERILOG_MODELS
`endif

/* `define DFT */

// Do not enable following for synthesis, only use for simulation
`ifdef VERILOG_MODELS
  `include "/users/micas/micas/design/tsmc28hpcplus/memories/Front_end/ts1n28hpcphvtb1024x32m4swbaso_180a/VERILOG/ts1n28hpcphvtb1024x32m4swbaso_180a_tt0p9v25c.v"
  `include "/users/micas/micas/design/tsmc28hpcplus/memories/Front_end/ts1n28hpcphvtb512x32m4swbaso_180a/VERILOG/ts1n28hpcphvtb512x32m4swbaso_180a_tt0p9v25c.v"
//  `include "/users/micas/micas/design/tsmc28hpcplus/memories/Front_end/ts1n28hpcphvtb256x32m4swbaso_180a/VERILOG/ts1n28hpcphvtb256x32m4swbaso_180a_tt0p9v25c.v"
  `include "/users/micas/micas/design/tsmc28hpcplus/memories/Front_end/ts1n28hpcphvtb1024x24m4swbaso_180a/VERILOG/ts1n28hpcphvtb1024x24m4swbaso_180a_tt0p9v25c.v"
  `include "/users/micas/micas/design/tsmc28hpcplus/memories/Front_end/ts1n28hpcphvtb512x24m4swbaso_180a/VERILOG/ts1n28hpcphvtb512x24m4swbaso_180a_tt0p9v25c.v"
//  `include "/users/micas/micas/design/tsmc28hpcplus/memories/Front_end/ts1n28hpcphvtb256x24m4swbaso_180a/VERILOG/ts1n28hpcphvtb256x24m4swbaso_180a_tt0p9v25c.v"
  `include "/users/micas/micas/design/tsmc28hpcplus/libs/TSMCHOME/digital/Front_End/verilog/tphn28hpcpgv18_110a/tphn28hpcpgv18.v"
`endif

package hw_pkg;
  parameter RESET_STATE         = 0;
`ifdef DESIGN_EXPLORE  
  parameter N_PE                = 64;
  parameter DATA_L              = 32;

  // global mem
  parameter N_GLOBAL_MEM_BANKS  = N_PE; // NOTE : interconnect_top has to be modified to allow any other value

  /* parameter GLOBAL_MEM_BANK_DEPTH= 1024; */
  /* parameter GLOBAL_MEM_BANK_DEPTH= 8192; */
  parameter GLOBAL_MEM_BANK_DEPTH= 65536;
  parameter GLOBAL_MEM_ADDR_L   = $clog2(GLOBAL_MEM_BANK_DEPTH) + $clog2(N_PE) + 1;
  
  // config 
  parameter PRECISION_CONFIG_L  = 2;

  // func unit
  parameter REGBANK_SIZE        = 32;
  parameter REG_ADDR_L          = $clog2(REGBANK_SIZE);
 
  // instr parameters
  parameter OPCODE_L            = 4;
  parameter INSTR_L             = OPCODE_L + 3*REG_ADDR_L + 3;
  
  // local mem
  /* parameter LOCAL_MEM_ADDR_L    = 9; */
  /* parameter LOCAL_MEM_ADDR_L    = 13; */
  parameter LOCAL_MEM_ADDR_L    = 16;

  parameter LOCAL_MEM_INDICATOR_S= GLOBAL_MEM_ADDR_L - 1; 
  parameter LOCAL_MEM_INDICATOR_L= 1;
  parameter LOCAL_MEM_INDICATOR = 0; // An address should go to local mem if the MSB bit of addr is set to it

`else
  parameter N_PE                = 64;
  parameter DATA_L              = 32;

  // global mem
  parameter N_GLOBAL_MEM_BANKS  = N_PE; // NOTE : interconnect_top has to be modified to allow any other value

  parameter GLOBAL_MEM_BANK_DEPTH= 1024;
  parameter GLOBAL_MEM_ADDR_L   = $clog2(GLOBAL_MEM_BANK_DEPTH) + $clog2(N_PE) + 1;
  
  // config 
  parameter PRECISION_CONFIG_L  = 2;

  // func unit
  parameter REGBANK_SIZE        = 32;
  parameter REG_ADDR_L          = $clog2(REGBANK_SIZE);
 
  // instr parameters
  parameter OPCODE_L            = 4;
  parameter INSTR_L             = OPCODE_L + 3*REG_ADDR_L + 3;
  
  // local mem
  parameter LOCAL_MEM_ADDR_L    = 9;

  parameter LOCAL_MEM_INDICATOR_S= GLOBAL_MEM_ADDR_L - 1; 
  parameter LOCAL_MEM_INDICATOR_L= 1;
  parameter LOCAL_MEM_INDICATOR = 0; // An address should go to local mem if the MSB bit of addr is set to it
`endif


endpackage: hw_pkg  

import hw_pkg::*;

package pe_pkg;
  import hw_pkg::*;

  // ld/st
  parameter LD_DATA_FIFO_DEPTH = 16;
  parameter LD_STREAM_CNT_L    = 3*REG_ADDR_L; // Cannot be bigger than this, due to instr encoding simplification
  parameter MAX_OUTSTANDING_LD_REQ = 4;

  parameter ST_DATA_FIFO_DEPTH = 2;

  parameter LOCAL_MEM_RD_LATENCY = 1;
  
  // Instr
  parameter NOP_OPCODE               = 0;
  parameter SUM_OPCODE               = 1;
  parameter PROD_OPCODE              = 2;
  parameter LOCAL_BARRIER_OPCODE     = 3;
  parameter GLOBAL_BARRIER_OPCODE    = 4;
  parameter SET_LD_STREAM_LEN_OPCODE = 5;
  parameter PASS_OPCODE              = 6;
  parameter MAX_OPCODE               = 7;
  parameter MIN_OPCODE               = 8;
  
  parameter INPUT_REG_0_S = OPCODE_L;
  parameter INPUT_REG_0_L = REG_ADDR_L;
  parameter INPUT_REG_1_S = INPUT_REG_0_S + INPUT_REG_0_L;
  parameter INPUT_REG_1_L = REG_ADDR_L;
  parameter OUTPUT_REG_S  = INPUT_REG_1_S + INPUT_REG_1_L;
  parameter OUTPUT_REG_L  = REG_ADDR_L;
  parameter LD_0_EN_S     = OUTPUT_REG_S + OUTPUT_REG_L;
  parameter LD_1_EN_S     = LD_0_EN_S + 1;
  parameter ST_EN_S       = LD_1_EN_S + 1;
  
  parameter SET_LD_STREAM_LEN_S= OPCODE_L;
  parameter SET_LD_STREAM_LEN_L= LD_STREAM_CNT_L;

  // Config
  parameter PRECISION_CONFIG_32B= 0;
  parameter PRECISION_CONFIG_16B= 1;
  parameter PRECISION_CONFIG_8B= 2;

endpackage: pe_pkg

package interconnect_pkg;
  import hw_pkg::*;
  parameter GLOBAL_MEM_PER_BANK_ADDR_L = GLOBAL_MEM_ADDR_L - $clog2(N_GLOBAL_MEM_BANKS) - 1;
  parameter GLOBAL_MEM_RD_LATENCY = 1;
  
  // starting position of bank id and bank addr in a global mem addr
  parameter BANK_ID_START= GLOBAL_MEM_PER_BANK_ADDR_L;
  parameter BANK_ADDR_START= 0;

endpackage: interconnect_pkg

package stream_pkg;
  import hw_pkg::*;
  
`ifdef DESIGN_EXPLORE  
  parameter INSTR_STR_ADDR_L= 16;
  parameter LD_STR_ADDR_L= 16;
  parameter ST_STR_ADDR_L= 16;
`else
  parameter INSTR_STR_ADDR_L= 10;
  parameter LD_STR_ADDR_L= 10;
  parameter ST_STR_ADDR_L= 9;
`endif
  
  parameter INSTR_STR_WORD_L= INSTR_L;
  parameter LD_STR_WORD_L= GLOBAL_MEM_ADDR_L + REG_ADDR_L;
  parameter ST_STR_WORD_L= GLOBAL_MEM_ADDR_L;

  parameter STR_RD_LATENCY= 1;
endpackage: stream_pkg

package periphery_pkg;
  import hw_pkg::*;
  
  // ADDR_TYPE bits are in the MSBs
  parameter ADDR_TYPE_L= 2;
  parameter ADDR_TYPE_STREAM= 0;
  parameter ADDR_TYPE_GLOBAL= 1;
  parameter ADDR_TYPE_LOCAL = 2;

  parameter IO_OPCODE_L               = 4;
  parameter IO_OPCODE_NOP             = 0;
  parameter IO_OPCODE_RD_EN           = 1;
  parameter IO_OPCODE_WR_EN           = 2;
  parameter IO_OPCODE_CONFIG_SHIFT_EN = 3;
  parameter IO_OPCODE_MONITOR         = 4;
  parameter IO_OPCODE_REG_SHIFT_EN    = 5;
  
  parameter INPUT_DATA_L = 16;
  parameter OUTPUT_DATA_L= 32;
  parameter INPUT_REG_L  = 64;
  
  parameter MONITOR_OPCODE_L   = 5;
  parameter MONITOR_OPCODE_NOP = 0;
  parameter MONITOR_OPCODE_GLOBAL_RD_REQ_0 = 1;
  parameter MONITOR_OPCODE_GLOBAL_RD_REQ_1 = 2;
  parameter MONITOR_OPCODE_GLOBAL_WR_REQ_0 = 3;
  parameter MONITOR_OPCODE_GLOBAL_WR_REQ_1 = 4;
  parameter MONITOR_OPCODE_GLOBAL_RD_GNT_0 = 5;
  parameter MONITOR_OPCODE_GLOBAL_RD_GNT_1 = 6;
  parameter MONITOR_OPCODE_GLOBAL_WR_GNT_0 = 7;
  parameter MONITOR_OPCODE_GLOBAL_WR_GNT_1 = 8;

  parameter MONITOR_OPCODE_INSTR_STREAM_REQ_0 = 9;
  parameter MONITOR_OPCODE_INSTR_STREAM_REQ_1 = 10;
  parameter MONITOR_OPCODE_LD_STREAM_REQ_0    = 11;
  parameter MONITOR_OPCODE_LD_STREAM_REQ_1    = 12;
  parameter MONITOR_OPCODE_ST_STREAM_REQ_0    = 13;
  parameter MONITOR_OPCODE_ST_STREAM_REQ_1    = 14;
  parameter MONITOR_OPCODE_INSTR_STREAM_GNT_0 = 15;
  parameter MONITOR_OPCODE_INSTR_STREAM_GNT_1 = 16;
  parameter MONITOR_OPCODE_LD_STREAM_GNT_0    = 17;
  parameter MONITOR_OPCODE_LD_STREAM_GNT_1    = 18;
  parameter MONITOR_OPCODE_ST_STREAM_GNT_0    = 19;
  parameter MONITOR_OPCODE_ST_STREAM_GNT_1    = 20;

  parameter MONITOR_OPCODE_POSIT_OUT= 21;
  parameter MONITOR_OPCODE_INSTR= 22;

endpackage: periphery_pkg

`endif //COMMON_DEF
