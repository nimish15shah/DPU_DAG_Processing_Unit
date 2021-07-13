//=======================================================================
// Created by         : KU Leuven
// Filename           : interconnection_top.sv
// Author             : Nimish Shah
// Created On         : 2019-12-11 09:59
// Last Modified      : 
// Update Count       : 2019-12-11 09:59
// Description        : 
//                      
//=======================================================================

`ifndef INTERCONNECT_TOP_DEF
  `define INTERCONNECT_TOP_DEF

`include "common.sv"
`include "interconnect_datapath_symmetric.sv"
`include "arbiter.sv"

module interconnect_top (
  input clk,
  input rst,
  
  // interface to PEs
  input [N_PE - 1 : 0] [GLOBAL_MEM_ADDR_L - 1 : 0] ld_addr,
  input [N_PE - 1 : 0]                             ld_req,
  output [N_PE - 1 : 0]                            ld_gnt,

  output [N_PE - 1 : 0] [DATA_L - 1 : 0]           ld_data,
  output [N_PE - 1 : 0]                            ld_data_vld,

  input [N_PE - 1 : 0] [interconnect_pkg::GLOBAL_MEM_PER_BANK_ADDR_L - 1 : 0] st_addr,
  input [N_PE - 1 : 0] [DATA_L - 1 : 0]            st_data,
  input [N_PE - 1 : 0]                             st_req,
  output [N_PE - 1 : 0]                            st_gnt,
  
  // interface to memory banks
  output [N_GLOBAL_MEM_BANKS - 1 : 0] [interconnect_pkg::GLOBAL_MEM_PER_BANK_ADDR_L - 1 : 0] mem_addr,
  output [N_GLOBAL_MEM_BANKS -1 : 0] [DATA_L - 1 : 0]                                        mem_wr_data,
  output [N_GLOBAL_MEM_BANKS - 1 : 0]                                                        mem_wr_en,
  output [N_GLOBAL_MEM_BANKS - 1 : 0]                                                        mem_rd_en,
  input [N_GLOBAL_MEM_BANKS - 1 : 0] [DATA_L - 1 : 0]                                        mem_rd_data,

  // Interface used to initialize the global memory
  input [GLOBAL_MEM_ADDR_L - 1 : 0]  init_mem_addr,
  input                              init_mem_vld,
  input                              init_mem_wr_en,
  input [DATA_L - 1 : 0]             init_mem_wr_data,
  output [DATA_L - 1 : 0]            init_mem_rd_data,
  output                             init_mem_rd_data_vld

); 
  import interconnect_pkg::*;
  
  logic [N_PE -1 : 0]  ld_gnt_pre;
  logic [N_PE -1 : 0]  st_gnt_pre;
  logic [N_GLOBAL_MEM_BANKS - 1 : 0][$clog2(N_PE) : 0] granted_requester_id;
  logic [N_GLOBAL_MEM_BANKS - 1 : 0]                       grant_out_port_wise;

  logic [N_PE -1 : 0][$clog2(N_GLOBAL_MEM_BANKS) - 1 : 0] ld_bank_id;
  logic [N_PE -1 : 0][GLOBAL_MEM_PER_BANK_ADDR_L - 1 : 0] ld_bank_addr;
  logic [N_PE -1 : 0][$clog2(N_GLOBAL_MEM_BANKS) - 1 : 0] st_bank_id;
  logic [N_PE -1 : 0][GLOBAL_MEM_PER_BANK_ADDR_L - 1 : 0] st_bank_addr;
  
  logic [N_PE - 1 : 0] ld_req_gated;
  logic [N_PE - 1 : 0] st_req_gated;
  
  assign ld_req_gated = init_mem_vld ? '0 : ld_req;
  assign st_req_gated = init_mem_vld ? '0 : st_req;

  logic [$clog2(N_GLOBAL_MEM_BANKS) - 1 : 0] init_bank_id;
  logic [GLOBAL_MEM_PER_BANK_ADDR_L - 1 : 0] init_bank_addr;

  //===========================================
  //      Combinational 
  //===========================================
  always_comb begin
    foreach ( ld_bank_id[i]) begin
      ld_bank_id[i] = ld_addr[i][BANK_ID_START +: $clog2(N_GLOBAL_MEM_BANKS)];
      ld_bank_addr[i] =  ld_addr[i][BANK_ADDR_START +: GLOBAL_MEM_PER_BANK_ADDR_L];
    end
  end
  always_comb begin
    foreach ( st_bank_id[i]) begin
      st_bank_addr[i] =  st_addr[i][BANK_ADDR_START +: GLOBAL_MEM_PER_BANK_ADDR_L];
      st_bank_id[i] = st_bank_addr[i][0 +: $clog2(N_GLOBAL_MEM_BANKS)];
    end
  end
  
  assign init_bank_id = init_mem_addr[BANK_ID_START +: $bits(init_bank_id)];
  assign init_bank_addr = init_mem_addr[BANK_ADDR_START +: $bits(init_bank_addr)];

  //===========================================
  //      Instances 
  //===========================================
  crossbar_arbiter #(
    .N_IN_PORTS (2*N_PE),
    .N_OUT_PORTS (N_GLOBAL_MEM_BANKS)
  ) ARBITER_INS (
      .clk                 (clk),
      .rst                 (rst),
      .req                 ({ld_req_gated, st_req_gated}),
      .req_out_port        ({ld_bank_id, st_bank_id}),
      .grant               ({ld_gnt_pre,st_gnt_pre}),

      .grant_out_port_wise (grant_out_port_wise),
      .detailed_grant      (),
      .granted_requester_id(granted_requester_id)
  );

  interconnect_datapath INTERCONNECT_DATAPATH_INS(
    .clk                 (clk),
    .rst                 (rst),

    .ld_mem_bank_id      (ld_bank_id),
    .ld_bank_addrs       (ld_bank_addr),
    .ld_gnt              (ld_gnt_pre),

    .granted_requester_id(granted_requester_id),
    .grant_out_port_wise (grant_out_port_wise),

    .ld_data             (ld_data),
    .ld_data_vld         (ld_data_vld),

    .st_bank_addrs       (st_bank_addr),
    .st_data             (st_data),

    .init_bank_id         (init_bank_id         ),
    .init_bank_addr       (init_bank_addr       ),
    .init_mem_vld         (init_mem_vld         ),
    .init_mem_wr_en       (init_mem_wr_en       ),
    .init_mem_wr_data     (init_mem_wr_data     ),
    .init_mem_rd_data     (init_mem_rd_data     ),
    .init_mem_rd_data_vld (init_mem_rd_data_vld ),

    .mem_addr            (mem_addr),
    .mem_wr_data         (mem_wr_data),
    .mem_wr_en           (mem_wr_en),
    .mem_rd_en           (mem_rd_en),
    .mem_rd_data         (mem_rd_data)
  );
  
  assign ld_gnt = ld_gnt_pre;
  assign st_gnt = st_gnt_pre;

  assert property (@(posedge clk) N_GLOBAL_MEM_BANKS == N_PE) else $warning("Interconnect is designed with this assumption. Store connection have to be modified to handle other casses");
  
  always_ff @(posedge clk ) begin
    foreach (ld_data_vld[i]) begin
      if (ld_data_vld[i]) begin
        assert (!$isunknown(ld_data[i]));
      end
    end
    foreach (ld_req[i]) begin
      if (ld_req[i]) begin
        assert (!$isunknown(ld_addr[i]));
      end
    end
    foreach (st_req[i]) begin
      if (st_req[i]) begin
        assert (!$isunknown(st_addr[i]));
        assert (!$isunknown(st_data[i]));
      end
    end
  end

endmodule


`endif //INTERCONNECT_TOP_DEF
