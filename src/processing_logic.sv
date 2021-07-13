//=======================================================================
// Created by         : KU Leuven
// Filename           : processing_logic.sv
// Author             : Nimish Shah
// Created On         : 2019-12-11 20:31
// Last Modified      : 
// Update Count       : 2019-12-11 20:31
// Description        : 
//                      
//=======================================================================


`ifndef PROCESSING_LOGIC_DEF
  `define PROCESSING_LOGIC_DEF

`include "common.sv"  

`include "interconnect_top.sv"
//`include "interconnect_top_symmetric.sv"
`include "pe_top.sv"

module processing_logic (
  input clk,
  input rst,

  input [N_PE - 1 : 0] config_local_mem_slp,
  input [N_PE - 1 : 0] config_local_mem_sd,
  
  // config
  input [PRECISION_CONFIG_L - 1 : 0] precision_config,

  // instructions and addrs
  input [N_PE - 1 : 0] [INSTR_L - 1 : 0]    instr, 
  input [N_PE - 1 : 0]                      instr_req,
  output[N_PE - 1 : 0]                      instr_ack,

  input [N_PE - 1 : 0] [GLOBAL_MEM_ADDR_L - 1 : 0] st_mem_addr_in,
  input [N_PE - 1 : 0]                             st_mem_addr_in_req,
  output[N_PE - 1 : 0]                             st_mem_addr_in_ack,

  input [N_PE - 1 : 0] [GLOBAL_MEM_ADDR_L - 1 : 0] ld_mem_addr_in,
  input [N_PE - 1 : 0] [REG_ADDR_L - 1: 0]         ld_reg_addr_in,
  input [N_PE - 1 : 0]                             ld_mem_addr_in_req,
  output[N_PE - 1 : 0]                             ld_mem_addr_in_ack,

  // global memory
  output [N_GLOBAL_MEM_BANKS - 1 : 0] [interconnect_pkg::GLOBAL_MEM_PER_BANK_ADDR_L - 1 : 0] global_mem_addr,
  output [N_GLOBAL_MEM_BANKS -1 : 0] [DATA_L - 1 : 0] global_mem_wr_data,
  output [N_GLOBAL_MEM_BANKS - 1 : 0]                 global_mem_wr_en,
  output [N_GLOBAL_MEM_BANKS - 1 : 0]                 global_mem_rd_en,
  input [N_GLOBAL_MEM_BANKS - 1 : 0] [DATA_L - 1 : 0] global_mem_rd_data,

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

  // monitor
  input monitor, 
  output [N_PE - 1 : 0] monitor_global_rd_req,
  output [N_PE - 1 : 0] monitor_global_rd_gnt,
  output [N_PE - 1 : 0] monitor_global_wr_req,
  output [N_PE - 1 : 0] monitor_global_wr_gnt,
  output [N_PE - 1 : 0] [DATA_L - 1 : 0] monitor_pe_out,
  output [N_PE - 1 : 0] [INSTR_L - 1 : 0] monitor_instr

); 

  //===========================================
  //      Signals 
  //===========================================
  logic [N_PE - 1 : 0] global_barrier_reached;
  logic global_barrier_reached_by_all_pes;

  logic [N_PE - 1 : 0] [GLOBAL_MEM_ADDR_L - 1 : 0] ld_addr;
  logic [N_PE - 1 : 0]                             ld_req;
  logic  [N_PE - 1 : 0]                            ld_gnt;

  logic  [N_PE - 1 : 0] [DATA_L - 1 : 0]           ld_data;
  logic  [N_PE - 1 : 0]                            ld_data_vld;

  logic [N_PE - 1 : 0] [interconnect_pkg::GLOBAL_MEM_PER_BANK_ADDR_L - 1 : 0] st_addr_trimmed;
  logic [N_PE - 1 : 0] [GLOBAL_MEM_ADDR_L - 1 : 0] st_addr;
  logic [N_PE - 1 : 0] [DATA_L - 1 : 0]            st_data;
  logic [N_PE - 1 : 0]                             st_req ;
  logic  [N_PE - 1 : 0]                            st_gnt ;

  assign global_barrier_reached_by_all_pes = ~global_barrier_reached ? 0 : 1;

  always_comb begin
    foreach ( st_addr_trimmed[i]) begin
      st_addr_trimmed[i] = st_addr[i][interconnect_pkg::GLOBAL_MEM_PER_BANK_ADDR_L - 1 : 0];
    end
  end


  //===========================================
  //      Instances 
  //===========================================
  interconnect_top INTERCONNECT_TOP_INS (
    .clk        (clk),
    .rst        (rst),

    .ld_addr    (ld_addr    ),
    .ld_req     (ld_req     ),
    .ld_gnt     (ld_gnt     ),
                            
    .ld_data    (ld_data    ),
    .ld_data_vld(ld_data_vld),
                            
    .st_addr    (st_addr_trimmed),
    .st_data    (st_data    ),
    .st_req     (st_req     ),
    .st_gnt     (st_gnt     ),

    .mem_addr   (global_mem_addr),
    .mem_wr_data(global_mem_wr_data),
    .mem_wr_en  (global_mem_wr_en),
    .mem_rd_en  (global_mem_rd_en),
    .mem_rd_data(global_mem_rd_data),

    .init_mem_addr        (init_global_mem_addr        ),
    .init_mem_vld         (init_global_mem_vld         ),
    .init_mem_wr_en       (init_global_mem_wr_en       ),
    .init_mem_wr_data     (init_global_mem_wr_data     ),
    .init_mem_rd_data     (init_global_mem_rd_data     ),
    .init_mem_rd_data_vld (init_global_mem_rd_data_vld )

  );

  generate
    genvar pe_i;
    for (pe_i=0; pe_i< N_PE; pe_i=pe_i+1) begin: pe_loop

      pe_top PE_TOP_INS (
        .clk                   (clk),
        .rst                   (rst),
        
        .config_local_mem_slp (config_local_mem_slp [pe_i]),
        .config_local_mem_sd  (config_local_mem_sd  [pe_i]),

        .instr                 (instr    [pe_i]),
        .instr_req             (instr_req[pe_i]),
        .instr_ack             (instr_ack[pe_i]),

        .global_barrier_reached(global_barrier_reached[pe_i]),
        .global_barrier_reached_by_all_pes(global_barrier_reached_by_all_pes),

        .precision_config      (precision_config),

        .st_mem_addr_in        (st_mem_addr_in    [pe_i]),
        .st_mem_addr_in_req    (st_mem_addr_in_req[pe_i]),
        .st_mem_addr_in_ack    (st_mem_addr_in_ack[pe_i]),

        .st_global_mem_addr    (st_addr[pe_i]),
        .st_global_mem_data    (st_data[pe_i]),
        .st_global_mem_st_req  (st_req [pe_i]),
        .st_global_mem_st_gnt  (st_gnt [pe_i]),

        .ld_mem_addr_in        (ld_mem_addr_in    [pe_i]),
        .ld_reg_addr_in        (ld_reg_addr_in    [pe_i]),
        .ld_mem_addr_in_req    (ld_mem_addr_in_req[pe_i]),
        .ld_mem_addr_in_ack    (ld_mem_addr_in_ack[pe_i]),

        .ld_global_mem_addr    (ld_addr[pe_i]),
        .ld_global_mem_addr_req(ld_req [pe_i]),
        .ld_global_mem_addr_gnt(ld_gnt [pe_i]),

        .ld_global_mem_data    (ld_data[pe_i]),
        .ld_global_mem_data_vld(ld_data_vld[pe_i]),

        .init_local_mem_addr        (init_local_mem_addr        ),
        .init_local_mem_wr_data     (init_local_mem_wr_data     ),
        .init_local_mem_vld         (init_local_mem_vld [pe_i]         ),
        .init_local_mem_wr_en       (init_local_mem_wr_en [pe_i]      ),
        .init_local_mem_rd_data     (init_local_mem_rd_data [pe_i]    ),
        .init_local_mem_rd_data_vld (init_local_mem_rd_data_vld [pe_i]),

        .monitor       (monitor),
        .monitor_pe_out(monitor_pe_out[pe_i]),
        .monitor_instr (monitor_instr [pe_i])
      );
    end
  endgenerate

  assign monitor_global_rd_req = ld_req;
  assign monitor_global_rd_gnt = ld_gnt;
  assign monitor_global_wr_req = st_req;
  assign monitor_global_wr_gnt = st_gnt;

endmodule

`endif


