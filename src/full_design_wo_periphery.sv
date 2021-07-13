//=======================================================================
// Created by         : KU Leuven
// Filename           : full_design_wo_periphery.sv
// Author             : Nimish Shah
// Created On         : 2020-01-09 10:19
// Last Modified      : 
// Update Count       : 2020-01-09 10:19
// Description        : 
//                      
//=======================================================================

`ifndef FULL_DESIGN_WO_PERIPHERY_DEF
  `define FULL_DESIGN_WO_PERIPHERY_DEF

  `include "common.sv"
  `include "processing_logic.sv"
  `include "global_mem.sv"
  `include "streams_top.sv"

module full_design_wo_periphery (
  input clk,
  input rst,

  input [N_PE - 1 : 0] config_local_mem_slp,
  input [N_PE - 1 : 0] config_local_mem_sd,

  input [N_PE - 1 : 0] config_global_mem_slp,
  input [N_PE - 1 : 0] config_global_mem_sd,

  input [N_PE - 1 : 0] config_stream_instr_slp,
  input [N_PE - 1 : 0] config_stream_ld_slp,
  input [N_PE - 1 : 0] config_stream_st_slp,

  input [N_PE - 1 : 0] config_stream_instr_sd,
  input [N_PE - 1 : 0] config_stream_ld_sd,
  input [N_PE - 1 : 0] config_stream_st_sd,

  input [GLOBAL_MEM_ADDR_L - 1 : 0]  init_global_mem_addr,
  input                              init_global_mem_vld,
  input                              init_global_mem_wr_en,
  input [DATA_L - 1 : 0]             init_global_mem_wr_data,
  output [DATA_L - 1 : 0]            init_global_mem_rd_data,
  output                             init_global_mem_rd_data_vld,

  input [LOCAL_MEM_ADDR_L - 1 : 0]      init_local_mem_addr,
  input [DATA_L - 1 : 0]                init_local_mem_wr_data,
  input  [N_PE - 1 : 0]                 init_local_mem_vld,
  input  [N_PE - 1 : 0]                 init_local_mem_wr_en,
  output [N_PE - 1 : 0][DATA_L - 1 : 0] init_local_mem_rd_data,
  output [N_PE - 1 : 0]                 init_local_mem_rd_data_vld,

  input [DATA_L - 1 : 0]                                         init_stream_wr_data,
  input [$clog2(N_PE) +stream_pkg::INSTR_STR_ADDR_L + 2 - 1 : 0] init_stream_addr,
  input                                                          init_stream_wr_vld,
  input                                                          init_stream_rd_vld,
  output [DATA_L - 1 : 0]                                        init_stream_rd_data,
  output                                                         init_stream_rd_data_vld,

  input [N_PE - 1 : 0][stream_pkg::INSTR_STR_ADDR_L - 1 : 0] instr_stream_start_addr_io,
  input [N_PE - 1 : 0][stream_pkg::INSTR_STR_ADDR_L - 1 : 0] instr_stream_end_addr_io,

  input [N_PE - 1 : 0][stream_pkg::LD_STR_ADDR_L - 1 : 0]    ld_stream_start_addr_io,
  input [N_PE - 1 : 0][stream_pkg::LD_STR_ADDR_L - 1 : 0]    ld_stream_end_addr_io,

  input [N_PE - 1 : 0][stream_pkg::ST_STR_ADDR_L - 1 : 0]    st_stream_start_addr_io,
  input [N_PE - 1 : 0][stream_pkg::ST_STR_ADDR_L - 1 : 0]    st_stream_end_addr_io,

  input [PRECISION_CONFIG_L - 1 : 0] precision_config,

  input                   reset_execution_io,
  input                   enable_execution_io,
  output                  done_execution_io,

  // monitor
  input monitor, 
  output [N_PE - 1 : 0] monitor_global_rd_req,
  output [N_PE - 1 : 0] monitor_global_rd_gnt,
  output [N_PE - 1 : 0] monitor_global_wr_req,
  output [N_PE - 1 : 0] monitor_global_wr_gnt,

  output [N_PE - 1 : 0] monitor_instr_stream_req,
  output [N_PE - 1 : 0] monitor_instr_stream_gnt,
  output [N_PE - 1 : 0] monitor_ld_stream_req,
  output [N_PE - 1 : 0] monitor_ld_stream_gnt,
  output [N_PE - 1 : 0] monitor_st_stream_req,
  output [N_PE - 1 : 0] monitor_st_stream_gnt,

  output [N_PE - 1 : 0] [DATA_L - 1 : 0] monitor_pe_out,
  output [N_PE - 1 : 0] [INSTR_L - 1 : 0] monitor_instr
);

  logic [N_GLOBAL_MEM_BANKS - 1 : 0] [interconnect_pkg::GLOBAL_MEM_PER_BANK_ADDR_L - 1 : 0] global_mem_addr;
  logic [N_GLOBAL_MEM_BANKS -1 : 0] [DATA_L - 1 : 0] global_mem_wr_data;
  logic [N_GLOBAL_MEM_BANKS - 1 : 0]                 global_mem_wr_en;
  logic [N_GLOBAL_MEM_BANKS - 1 : 0]                 global_mem_rd_en; 
  logic  [N_GLOBAL_MEM_BANKS - 1 : 0] [DATA_L - 1 : 0] global_mem_rd_data;

  logic [N_PE - 1 : 0][stream_pkg::INSTR_STR_WORD_L - 1 : 0] instr;
  logic [N_PE - 1 : 0]                                       instr_vld;
  logic [N_PE - 1 : 0]                                       instr_rdy;

  logic [N_PE - 1 : 0][stream_pkg::LD_STR_WORD_L - 1 : 0]    ld_addr;
  logic [N_PE - 1 : 0]                                       ld_addr_vld;
  logic [N_PE - 1 : 0]                                       ld_addr_rdy;

  logic [N_PE - 1 : 0][stream_pkg::ST_STR_WORD_L - 1 : 0]    st_addr;
  logic [N_PE - 1 : 0]                                       st_addr_vld;
  logic [N_PE - 1 : 0]                                       st_addr_rdy;

  logic [N_PE - 1 : 0] [GLOBAL_MEM_ADDR_L - 1 : 0] ld_mem_addr;
  logic [N_PE - 1 : 0] [REG_ADDR_L - 1: 0]         ld_reg_addr;
  
  always_comb begin
    foreach (ld_addr[i]) begin
      {ld_reg_addr[i], ld_mem_addr[i]} = ld_addr[i];
    end
  end


  processing_logic PROCESSING_LOGIC_INS (
    .clk                         (clk             ),
    .rst                         (rst             ),
                                                  
    .config_local_mem_slp (config_local_mem_slp ),
    .config_local_mem_sd  (config_local_mem_sd  ),

    .precision_config            (precision_config),

    .instr                       (instr    ),
    .instr_req                   (instr_vld),
    .instr_ack                   (instr_rdy),

    .st_mem_addr_in              (st_addr    ),
    .st_mem_addr_in_req          (st_addr_vld),
    .st_mem_addr_in_ack          (st_addr_rdy),

    .ld_mem_addr_in              (ld_mem_addr),
    .ld_reg_addr_in              (ld_reg_addr),
    .ld_mem_addr_in_req          (ld_addr_vld),
    .ld_mem_addr_in_ack          (ld_addr_rdy),

    .global_mem_addr             (global_mem_addr   ),
    .global_mem_wr_data          (global_mem_wr_data),
    .global_mem_wr_en            (global_mem_wr_en  ),
    .global_mem_rd_en            (global_mem_rd_en  ),
    .global_mem_rd_data          (global_mem_rd_data),

    .init_global_mem_addr        (init_global_mem_addr       ),
    .init_global_mem_vld         (init_global_mem_vld        ),
    .init_global_mem_wr_en       (init_global_mem_wr_en      ),
    .init_global_mem_wr_data     (init_global_mem_wr_data    ),
    .init_global_mem_rd_data     (init_global_mem_rd_data    ),
    .init_global_mem_rd_data_vld (init_global_mem_rd_data_vld),
                                                             
    .init_local_mem_addr         (init_local_mem_addr        ),
    .init_local_mem_wr_data      (init_local_mem_wr_data     ),
    .init_local_mem_vld          (init_local_mem_vld         ),
    .init_local_mem_wr_en        (init_local_mem_wr_en       ),
    .init_local_mem_rd_data      (init_local_mem_rd_data     ),
    .init_local_mem_rd_data_vld  (init_local_mem_rd_data_vld ),

    .monitor       (monitor),
    .monitor_global_rd_req (monitor_global_rd_req),
    .monitor_global_rd_gnt (monitor_global_rd_gnt),
    .monitor_global_wr_req (monitor_global_wr_req),
    .monitor_global_wr_gnt (monitor_global_wr_gnt),

    .monitor_pe_out(monitor_pe_out),
    .monitor_instr (monitor_instr)
  ); 

  global_mem GLOBAL_MEM_INS (
    .clk                (clk               ),
    .rst                (rst               ),

    .config_global_mem_slp (config_global_mem_slp),  
    .config_global_mem_sd  (config_global_mem_sd),

    .global_mem_addr    (global_mem_addr   ),
    .global_mem_wr_data (global_mem_wr_data),
    .global_mem_wr_en   (global_mem_wr_en  ),
    .global_mem_rd_en   (global_mem_rd_en  ),
    .global_mem_rd_data (global_mem_rd_data)
  ); 

  streams_top STREAMS_TOP_INS (
    .clk                        (clk),
    .rst                        (rst),

    .config_stream_instr_slp (config_stream_instr_slp),
    .config_stream_ld_slp    (config_stream_ld_slp   ),
    .config_stream_st_slp    (config_stream_st_slp   ),
                                                     
    .config_stream_instr_sd  (config_stream_instr_sd ),
    .config_stream_ld_sd     (config_stream_ld_sd    ),
    .config_stream_st_sd     (config_stream_st_sd    ),

    .monitor_instr_stream_req (monitor_instr_stream_req),
    .monitor_instr_stream_gnt (monitor_instr_stream_gnt),
    .monitor_ld_stream_req    (monitor_ld_stream_req   ),
    .monitor_ld_stream_gnt    (monitor_ld_stream_gnt   ),
    .monitor_st_stream_req    (monitor_st_stream_req   ),
    .monitor_st_stream_gnt    (monitor_st_stream_gnt   ),

    .wr_data_io                 (init_stream_wr_data    ),
    .full_addr_io               (init_stream_addr       ),
    .wr_vld_io                  (init_stream_wr_vld     ),
    .rd_vld_io                  (init_stream_rd_vld     ),

    .rd_data_io                 (init_stream_rd_data    ),
    .rd_data_vld_io             (init_stream_rd_data_vld),

    .reset_execution_io         (reset_execution_io ),
    .enable_execution_io        (enable_execution_io),
    .done_execution_io          (done_execution_io  ),

    .instr_stream_start_addr_io (instr_stream_start_addr_io ),
    .instr_stream_end_addr_io   (instr_stream_end_addr_io   ),
                                                            
    .ld_stream_start_addr_io    (ld_stream_start_addr_io    ),
    .ld_stream_end_addr_io      (ld_stream_end_addr_io      ),
                                                            
    .st_stream_start_addr_io    (st_stream_start_addr_io    ),
    .st_stream_end_addr_io      (st_stream_end_addr_io      ),

    .instr                      (instr      ),
    .instr_vld                  (instr_vld  ),
    .instr_rdy                  (instr_rdy  ),
                                            
    .ld_addr                    (ld_addr    ),
    .ld_addr_vld                (ld_addr_vld),
    .ld_addr_rdy                (ld_addr_rdy),
                                            
    .st_addr                    (st_addr    ),
    .st_addr_vld                (st_addr_vld),
    .st_addr_rdy                (st_addr_rdy)
  ); 

endmodule

`endif //FULL_DESIGN_WO_PERIPHERY_DEF
