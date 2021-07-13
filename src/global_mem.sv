//=======================================================================
// Created by         : KU Leuven
// Filename           : global_mem.sv
// Author             : Nimish Shah
// Created On         : 2020-01-04 15:44
// Last Modified      : 
// Update Count       : 2020-01-04 15:44
// Description        : 
//                      
//=======================================================================

`ifndef GLOBAL_MEM_DEF
  `define GLOBAL_MEM_DEF

  `include "common.sv"
  `include "mem_model.sv"

module global_mem (
  input clk,
  input rst,

  input [N_GLOBAL_MEM_BANKS - 1 : 0] config_global_mem_slp,
  input [N_GLOBAL_MEM_BANKS - 1 : 0] config_global_mem_sd,

  input [N_GLOBAL_MEM_BANKS - 1 : 0] [interconnect_pkg::GLOBAL_MEM_PER_BANK_ADDR_L - 1 : 0] global_mem_addr,
  input [N_GLOBAL_MEM_BANKS -1 : 0] [DATA_L - 1 : 0] global_mem_wr_data,
  input [N_GLOBAL_MEM_BANKS - 1 : 0]                 global_mem_wr_en,
  input [N_GLOBAL_MEM_BANKS - 1 : 0]                 global_mem_rd_en, 
  output [N_GLOBAL_MEM_BANKS - 1 : 0] [DATA_L - 1 : 0] global_mem_rd_data
  
); 
  
  import interconnect_pkg::*;

  logic [N_GLOBAL_MEM_BANKS - 1 : 0] global_mem_ch_en;
  assign global_mem_ch_en = global_mem_wr_en | global_mem_rd_en;
  
  generate
    genvar mem_i;
    for (mem_i=0; mem_i< N_GLOBAL_MEM_BANKS ; mem_i=mem_i+1) begin: mem_loop
      sp_mem_model #(
        .DATA_L (DATA_L),
        .ADDR_L (GLOBAL_MEM_PER_BANK_ADDR_L),
        .RD_LATENCY (GLOBAL_MEM_RD_LATENCY)
      ) SP_MEM_MODEL_INS
      (
        .clk     (clk     ),
        .rst     (rst     ),

        .slp     (config_global_mem_slp[mem_i]),
        .sd      (config_global_mem_sd [mem_i]),
                          
        .wr_en   (global_mem_wr_en  [mem_i]),
        .addr    (global_mem_addr   [mem_i]),
        .wr_data (global_mem_wr_data[mem_i]),
        .rd_data (global_mem_rd_data[mem_i]),
        .ch_en   (global_mem_ch_en  [mem_i])
      ); 
    end
  endgenerate
endmodule


`endif //GLOBAL_MEM_DEF
