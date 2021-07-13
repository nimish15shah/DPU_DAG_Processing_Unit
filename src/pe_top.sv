//=======================================================================
// Created by         : KU Leuven
// Filename           : pe_top.sv
// Author             : Nimish Shah
// Created On         : 2019-12-09 15:50
// Last Modified      : 
// Update Count       : 2019-12-09 15:50
// Description        : 
//                      
//=======================================================================

`ifndef PE_TOP_DEF
  `define PE_TOP_DEF

`include "common.sv"
`include "pe_func_unit.sv"
`include "pe_ld_unit.sv"
`include "pe_st_unit.sv"
`include "local_mem_arbiter.sv"
`include "mem_model.sv"

module pe_top (
  input clk,
  input rst,

  input config_local_mem_slp,
  input config_local_mem_sd,

  // pe_func_unit
  input [INSTR_L - 1 : 0]    instr, 
  input                      instr_req,
  output                     instr_ack,

  output global_barrier_reached,
  input  global_barrier_reached_by_all_pes,

  input [PRECISION_CONFIG_L - 1 : 0] precision_config,

  // st unit
  input [GLOBAL_MEM_ADDR_L - 1 : 0] st_mem_addr_in,
  input                             st_mem_addr_in_req,
  output                            st_mem_addr_in_ack,

  output [GLOBAL_MEM_ADDR_L - 1 : 0] st_global_mem_addr,
  output [DATA_L - 1 : 0]            st_global_mem_data,
  output                             st_global_mem_st_req,
  input                              st_global_mem_st_gnt,

  // ld unit
  input [GLOBAL_MEM_ADDR_L - 1 : 0] ld_mem_addr_in,
  input [REG_ADDR_L - 1: 0]         ld_reg_addr_in,
  input                             ld_mem_addr_in_req,
  output                            ld_mem_addr_in_ack,
  
  output [GLOBAL_MEM_ADDR_L- 1 : 0] ld_global_mem_addr,
  output                            ld_global_mem_addr_req,
  input                             ld_global_mem_addr_gnt,

  input [DATA_L -1 : 0]             ld_global_mem_data,
  input                             ld_global_mem_data_vld,
  
  // Interface used to initialize the local memory
  input [LOCAL_MEM_ADDR_L - 1 : 0] init_local_mem_addr,
  input [DATA_L - 1 : 0]           init_local_mem_wr_data,
  input                            init_local_mem_vld,
  input                            init_local_mem_wr_en,
  output [DATA_L - 1 : 0]          init_local_mem_rd_data,
  output                           init_local_mem_rd_data_vld,

  // monitor
  input monitor,
  output [DATA_L - 1 : 0] monitor_pe_out,
  output [INSTR_L - 1 : 0] monitor_instr
); 

  //===========================================
  //      Signals 
  //===========================================
  logic [pe_pkg::LD_STREAM_CNT_L - 1 : 0] ld_stream_len;
  logic                                   ld_stream_len_vld;

  logic [DATA_L - 1 : 0]    st_data;
  logic                     st_req;
  logic                     st_ack;

  logic [DATA_L - 1 : 0]     ld_0_data;
  logic [REG_ADDR_L - 1 : 0] ld_0_addr;
  logic                      ld_0_vld;
  logic                      ld_0_rdy;

  logic [DATA_L - 1 : 0]     ld_1_data;
  logic [REG_ADDR_L - 1 : 0] ld_1_addr;
  logic                      ld_1_vld;
  logic                      ld_1_rdy;

  logic [LOCAL_MEM_ADDR_L - 1 : 0]  st_local_mem_addr;
  logic [DATA_L - 1 : 0]            st_local_mem_data;
  logic                             st_local_mem_st_req;
  logic                             st_local_mem_st_gnt;

  logic [LOCAL_MEM_ADDR_L - 1 : 0] ld_local_mem_addr;
  logic                            ld_local_mem_addr_req;
  logic                            ld_local_mem_addr_gnt;

  logic[DATA_L -1 : 0]             ld_local_mem_data;
  logic                            ld_local_mem_data_vld;

  logic [LOCAL_MEM_ADDR_L - 1 : 0] local_mem_addr;
  logic [DATA_L - 1 : 0]           local_mem_wr_data;
  logic                            local_mem_wr_en;
  logic                            local_mem_rd_en;
  logic                            local_mem_ch_en;
  logic [DATA_L - 1 : 0]           local_mem_rd_data;

  logic all_stored;
  
  assign local_mem_ch_en = local_mem_rd_en | local_mem_wr_en;
  //===========================================
  //      Instances 
  //===========================================
  pe_func_unit PE_FUNC_UNIT_INS (
    .clk                              (clk                              ),
    .rst                              (rst                              ),
                                                                        
    .instr                            (instr                            ),
    .instr_req                        (instr_req                        ),
    .instr_ack                        (instr_ack                        ),
                                                                        
    .ld_0_data                        (ld_0_data                        ),
    .ld_0_addr                        (ld_0_addr                        ),
    .ld_0_vld                         (ld_0_vld                         ),
    .ld_0_rdy                         (ld_0_rdy                         ),
                                                                        
    .ld_1_data                        (ld_1_data                        ),
    .ld_1_addr                        (ld_1_addr                        ),
    .ld_1_vld                         (ld_1_vld                         ),
    .ld_1_rdy                         (ld_1_rdy                         ),
                                                                        
    .st_data                          (st_data                          ),
    .st_req                           (st_req                           ),
    .st_ack                           (st_ack                           ),
                                                                        
    .ld_stream_len                    (ld_stream_len                    ),
    .ld_stream_len_vld                (ld_stream_len_vld                ),
                                                                        
    .all_stored                       (all_stored                       ),
                                                                        
    .global_barrier_reached           (global_barrier_reached           ),
    .global_barrier_reached_by_all_pes(global_barrier_reached_by_all_pes),
                                                                        
    .precision_config                 (precision_config                 ),
    
    .monitor       (monitor),
    .monitor_pe_out(monitor_pe_out),
    .monitor_instr (monitor_instr)
  );

  pe_st_unit PE_ST_UNIT (
    .clk              (clk              ),
    .rst              (rst              ),
                                        
    .mem_addr_in      (st_mem_addr_in      ),
    .mem_addr_in_req  (st_mem_addr_in_req  ),
    .mem_addr_in_ack  (st_mem_addr_in_ack  ),


    .global_mem_addr  (st_global_mem_addr  ),
    .global_mem_data  (st_global_mem_data  ),
    .global_mem_st_req(st_global_mem_st_req),
    .global_mem_st_gnt(st_global_mem_st_gnt),


    .local_mem_addr   (st_local_mem_addr   ),
    .local_mem_data   (st_local_mem_data   ),
    .local_mem_st_req (st_local_mem_st_req ),
    .local_mem_st_gnt (st_local_mem_st_gnt ),
                                        
    .fu_st_data       (st_data),
    .fu_st_data_req   (st_req),
    .fu_st_data_gnt   (st_ack),

    .all_stored       (all_stored)

  );

  pe_ld_unit PE_LD_UNIT_INS (
    .clk                (clk                ),
    .rst                (rst                ),
                                            
    .ld_stream_len      (ld_stream_len      ),
    .ld_stream_len_vld  (ld_stream_len_vld  ),
                                            
    .mem_addr_in        (ld_mem_addr_in        ),
    .reg_addr_in        (ld_reg_addr_in        ),
    .mem_addr_in_req    (ld_mem_addr_in_req    ),
    .mem_addr_in_ack    (ld_mem_addr_in_ack    ),
                      
                     
    .global_mem_addr    (ld_global_mem_addr    ),
    .global_mem_addr_req(ld_global_mem_addr_req),
    .global_mem_addr_gnt(ld_global_mem_addr_gnt),
                         
    .global_mem_data    (ld_global_mem_data    ),
    .global_mem_data_vld(ld_global_mem_data_vld),
                         
                         
    .local_mem_addr     (ld_local_mem_addr     ),
    .local_mem_addr_req (ld_local_mem_addr_req ),
    .local_mem_addr_gnt (ld_local_mem_addr_gnt ),
                         
    .local_mem_data     (ld_local_mem_data     ),
    .local_mem_data_vld (ld_local_mem_data_vld ),

    .reg_addr_out_0     (ld_0_addr),
    .data_out_0         (ld_0_data),
    .data_out_0_vld     (ld_0_vld),
    .data_out_0_rdy     (ld_0_rdy),

    .reg_addr_out_1     (ld_1_addr),
    .data_out_1         (ld_1_data),
    .data_out_1_vld     (ld_1_vld),
    .data_out_1_rdy     (ld_1_rdy)
  );

  local_mem_arbiter LOCAL_MEM_ARBITER_INS(
    .clk                  (clk),
    .rst                  (rst),

    .ld_local_mem_addr    (ld_local_mem_addr),
    .ld_local_mem_addr_req(ld_local_mem_addr_req),
    .ld_local_mem_addr_gnt(ld_local_mem_addr_gnt),
                                                
    .ld_local_mem_data    (ld_local_mem_data    ),
    .ld_local_mem_data_vld(ld_local_mem_data_vld),

    .st_local_mem_addr    (st_local_mem_addr    ),
    .st_local_mem_data    (st_local_mem_data    ),
    .st_local_mem_st_req  (st_local_mem_st_req  ),
    .st_local_mem_st_gnt  (st_local_mem_st_gnt  ),

    .local_mem_addr       (local_mem_addr   ),
    .local_mem_wr_data    (local_mem_wr_data),
    .local_mem_wr_en      (local_mem_wr_en  ),
    .local_mem_rd_en      (local_mem_rd_en  ),
    .local_mem_rd_data    (local_mem_rd_data),

    .init_local_mem_addr        (init_local_mem_addr        ),
    .init_local_mem_wr_data     (init_local_mem_wr_data     ),
    .init_local_mem_vld         (init_local_mem_vld         ),
    .init_local_mem_wr_en       (init_local_mem_wr_en       ),
    .init_local_mem_rd_data     (init_local_mem_rd_data     ),
    .init_local_mem_rd_data_vld (init_local_mem_rd_data_vld )
  );

  sp_mem_model #(
    .DATA_L (DATA_L),
    .ADDR_L (LOCAL_MEM_ADDR_L),
    .RD_LATENCY (pe_pkg::LOCAL_MEM_RD_LATENCY)
  ) SP_MEM_MODEL_INS
  (
    .clk     (clk     ),
    .rst     (rst     ),
                      
    .slp     (config_local_mem_slp),
    .sd      (config_local_mem_sd),

    .wr_en   (local_mem_wr_en   ),
    .ch_en   (local_mem_ch_en   ),
    .addr    (local_mem_addr    ),
    .wr_data (local_mem_wr_data ),
    .rd_data (local_mem_rd_data )
  ); 

endmodule


`endif //PE_TOP_DEF
