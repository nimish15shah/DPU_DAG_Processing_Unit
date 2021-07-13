//=======================================================================
// Created by         : KU Leuven
// Filename           : local_mem_arbiter.sv
// Author             : Nimish Shah
// Created On         : 2019-12-18 21:47
// Last Modified      : 
// Update Count       : 2019-12-18 21:47
// Description        : 
//                      
//=======================================================================

`ifndef LOCAL_MEM_ARBITER_DEF
  `define LOCAL_MEM_ARBITER_DEF

`include "common.sv"
`include "arbiter.sv"

  //===========================================
  //       assumption: Single-ported local mem
  //===========================================

module local_mem_arbiter (
  input clk,
  input rst,

  input [LOCAL_MEM_ADDR_L - 1 : 0] ld_local_mem_addr,
  input                            ld_local_mem_addr_req,
  output                           ld_local_mem_addr_gnt,

  output [DATA_L -1 : 0]           ld_local_mem_data,
  output                           ld_local_mem_data_vld,

  input [LOCAL_MEM_ADDR_L - 1 : 0] st_local_mem_addr,
  input [DATA_L - 1 : 0]           st_local_mem_data,
  input                            st_local_mem_st_req,
  output                           st_local_mem_st_gnt,

  output [LOCAL_MEM_ADDR_L - 1 : 0] local_mem_addr,
  output [DATA_L - 1 : 0]           local_mem_wr_data,
  output                            local_mem_wr_en,
  output                            local_mem_rd_en,
  input  [DATA_L - 1 : 0]           local_mem_rd_data,
  
  // Interface used to initialize the local memory
  input [LOCAL_MEM_ADDR_L - 1 : 0] init_local_mem_addr,
  input [DATA_L - 1 : 0]           init_local_mem_wr_data,
  input                            init_local_mem_vld,
  input                            init_local_mem_wr_en,
  output [DATA_L - 1 : 0]          init_local_mem_rd_data,
  output                           init_local_mem_rd_data_vld
  
); 
  
  logic [1:0] req;
  logic [1:0] req_gated;
  logic [1:0] gnt;
  logic ld_gnt;
  logic st_gnt;
  logic init_local_mem_rd_en;
  logic [LOCAL_MEM_ADDR_L - 1 : 0] local_mem_addr_pre;

  localparam DELAY = pe_pkg::LOCAL_MEM_RD_LATENCY;
  logic [DELAY - 1 : 0] ld_gnt_delayed;
  logic [DELAY - 1 : 0] init_rd_en_delayed;
    
  assign init_local_mem_rd_en = init_local_mem_vld ? ~init_local_mem_wr_en : 1'b0;

//  assign req[0] = ld_local_mem_addr_req;
  // creating high priority for store request
  assign req[0] = st_local_mem_st_req? '0 : ld_local_mem_addr_req;
  assign req[1] = st_local_mem_st_req;
  assign req_gated = init_local_mem_vld ? '0 : req;

  assign ld_gnt = gnt[0];
  assign st_gnt = gnt[1];

  always_comb begin
    if (ld_gnt) begin
      local_mem_addr_pre = ld_local_mem_addr;
    end else begin
      local_mem_addr_pre = st_local_mem_addr;
    end

    if (init_local_mem_vld) begin
      local_mem_addr_pre= init_local_mem_addr;
    end
  end

  always_ff @(posedge clk or negedge rst) begin
    if (rst== RESET_STATE) begin
      ld_gnt_delayed <= '0;
      init_rd_en_delayed <= '0;
    end else begin
      ld_gnt_delayed[0] <= ld_gnt;
      init_rd_en_delayed[0] <= init_local_mem_rd_en;
      for (integer i=1; i< DELAY ; i=i+1) begin
        ld_gnt_delayed [i] <= ld_gnt_delayed[i-1];
        init_rd_en_delayed[i] <= init_rd_en_delayed[i-1];
      end
    end
  end

  //===========================================
  //       Instances
  //===========================================
  simple_rr_arbiter #( .N_IN_PORTS(2) )
    RR_ARBITER_INS (
      .clk                 (clk),
      .rst                 (rst),
      .req                 (req_gated),
      .grant               (gnt),
      .granted_requester_id()
    );


  //===========================================
  //      Outputs 
  //===========================================
  assign st_local_mem_st_gnt= st_gnt;

  assign ld_local_mem_addr_gnt= ld_gnt;
  assign ld_local_mem_data = local_mem_rd_data;
  assign ld_local_mem_data_vld = ld_gnt_delayed[DELAY - 1];

  assign local_mem_addr = local_mem_addr_pre;
  assign local_mem_wr_en= init_local_mem_vld ? init_local_mem_wr_en : st_gnt;
  assign local_mem_rd_en= init_local_mem_vld ? init_local_mem_rd_en : ld_gnt;
  assign local_mem_wr_data= init_local_mem_vld ? init_local_mem_wr_data : st_local_mem_data;
  
  assign init_local_mem_rd_data = local_mem_rd_data;
  assign init_local_mem_rd_data_vld = init_rd_en_delayed[DELAY - 1];
//  assign init_st_local_mem_st_gnt = 1'b1;

  //===========================================
  //       Assertions
  //===========================================
  assert property (@(posedge clk) if(st_local_mem_st_gnt) (!ld_local_mem_addr_gnt)) else $warning("Both grants cannot be high together");

endmodule


`endif //LOCAL_MEM_ARBITER_DEF
