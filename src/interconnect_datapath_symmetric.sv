//=======================================================================
// Created by         : KU Leuven
// Filename           : interconnect_datapath.sv
// Author             : Nimish Shah
// Created On         : 2019-12-11 14:42
// Last Modified      : 
// Update Count       : 2019-12-11 14:42
// Description        : 
//                      
//=======================================================================

`ifndef INTERCONNECT_DATAPATH_DEF
  `define INTERCONNECT_DATAPATH_DEF

  `include "common.sv"

module interconnect_datapath (
  input clk, rst,

  input [N_PE - 1 : 0] [$clog2(N_GLOBAL_MEM_BANKS) - 1 : 0]                                  ld_mem_bank_id,
  input [N_PE - 1 : 0] [interconnect_pkg::GLOBAL_MEM_PER_BANK_ADDR_L - 1 : 0]                ld_bank_addrs,
  input [N_PE - 1 : 0]                                                                       ld_gnt,

  input [N_GLOBAL_MEM_BANKS - 1 : 0][$clog2(N_PE) : 0]                                   granted_requester_id,
  input [N_GLOBAL_MEM_BANKS - 1 : 0]                                                         grant_out_port_wise,

  output [N_PE - 1 : 0] [DATA_L - 1 : 0]                                                     ld_data,
  output [N_PE - 1 : 0]                                                                      ld_data_vld,

  input [N_PE - 1 : 0] [interconnect_pkg::GLOBAL_MEM_PER_BANK_ADDR_L- 1 : 0]                 st_bank_addrs,
  input [N_PE - 1 : 0] [DATA_L - 1 : 0]                                                      st_data,

  input [$clog2(N_GLOBAL_MEM_BANKS) - 1 : 0]                   init_bank_id,
  input [interconnect_pkg::GLOBAL_MEM_PER_BANK_ADDR_L - 1 : 0] init_bank_addr,
  input                                                        init_mem_vld,
  input                                                        init_mem_wr_en,
  input [DATA_L - 1 : 0]                                       init_mem_wr_data,
  output [DATA_L - 1 : 0]                                      init_mem_rd_data,
  output                                                       init_mem_rd_data_vld,

  output [N_GLOBAL_MEM_BANKS - 1 : 0] [interconnect_pkg::GLOBAL_MEM_PER_BANK_ADDR_L - 1 : 0] mem_addr,
  output [N_GLOBAL_MEM_BANKS -1 : 0] [DATA_L - 1 : 0]                                        mem_wr_data,
  output [N_GLOBAL_MEM_BANKS - 1 : 0]                                                        mem_wr_en,
  output [N_GLOBAL_MEM_BANKS - 1 : 0]                                                        mem_rd_en,
  input [N_GLOBAL_MEM_BANKS - 1 : 0] [DATA_L - 1 : 0]                                        mem_rd_data
); 
  
  logic [N_PE - 1 : 0] [DATA_L - 1 : 0]                                                     ld_data_pre;
  logic [N_PE - 1 : 0]                                                                      ld_data_vld_pre;

  logic [N_GLOBAL_MEM_BANKS - 1 : 0] init_mem_wr_en_decoded;
  logic [N_GLOBAL_MEM_BANKS - 1 : 0] init_mem_vld_decoded;

  always_comb begin
    init_mem_wr_en_decoded= '0;
    init_mem_vld_decoded= '0;
    init_mem_wr_en_decoded[init_bank_id] = init_mem_wr_en;
    init_mem_vld_decoded[init_bank_id] = init_mem_vld;
  end

  generate
    genvar bank_i;
    for (bank_i=0; bank_i< N_GLOBAL_MEM_BANKS; bank_i=bank_i+1) begin: incoming_datapath_loop
      interconnect_incoming_datapath_per_bank INTERCONNECT_INCOMING_DATAPATH_PER_BANK_INS (
        .ld_bank_addrs       (ld_bank_addrs       ),
        .granted_requester_id(granted_requester_id[bank_i]),
        .grant_out_port_wise (grant_out_port_wise[bank_i]),

        .st_bank_addrs        (st_bank_addrs),
        .st_data             (st_data ),
        
        .init_bank_addr   (init_bank_addr),
        .init_mem_vld     (init_mem_vld_decoded[bank_i]),
        .init_mem_wr_en   (init_mem_wr_en_decoded[bank_i]),
        .init_mem_wr_data (init_mem_wr_data),

        .mem_addr            (mem_addr [bank_i]   ),
        .mem_wr_data         (mem_wr_data [bank_i]),
        .mem_wr_en           (mem_wr_en[bank_i]),
        .mem_rd_en           (mem_rd_en[bank_i])
    );
    end
  endgenerate

  generate
    genvar pe_i;
    for (pe_i=0; pe_i< N_PE; pe_i=pe_i+1) begin: outgoing_datapath_loop
      interconnect_outgoing_datapath_per_pe INTERCONNECT_OUTGOING_DATAPATH_PER_PE_INS (
        .clk           (clk),
        .rst           (rst),
        .ld_mem_bank_id(ld_mem_bank_id[pe_i]),
        .ld_gnt        (ld_gnt[pe_i]),

        .mem_rd_data   (mem_rd_data),

        .ld_data       (ld_data_pre[pe_i ]),
        .ld_data_vld   (ld_data_vld_pre[pe_i])
      );
    end
  endgenerate
  
  interconnect_outgoing_datapath_init INTERCONNECT_OUTGOING_DATAPATH_INIT_INS (
    .clk                     (clk),
    .rst                     (rst),

    .mem_rd_data             (mem_rd_data),

    .init_bank_id     (init_bank_id     ),
    .init_mem_vld     (init_mem_vld     ),
    .init_mem_wr_en   (init_mem_wr_en   ),
    .init_mem_rd_data (init_mem_rd_data ),
    .init_mem_rd_data_vld (init_mem_rd_data_vld)
  );

  assign ld_data= ld_data_pre;
  assign ld_data_vld = ld_data_vld_pre;

  //===========================================
  //      Assertions 
  //===========================================
  always_ff @(posedge clk ) begin
    for (integer i=0; i<N_PE  ; i=i+1) begin
      for (integer j=0; j<N_PE  ; j=j+1) begin
        if (i != j && ld_gnt[i] == 1 && ld_gnt[j] == 1) begin
          assert (ld_mem_bank_id[i] != ld_mem_bank_id[j]) else $warning("Multiple PEs accessing same bank");
        end
      end
    end
  end

endmodule

module interconnect_incoming_datapath_per_bank (
  input [N_PE - 1 : 0] [interconnect_pkg::GLOBAL_MEM_PER_BANK_ADDR_L - 1 : 0] ld_bank_addrs,
  input [$clog2(N_PE) : 0]                                                granted_requester_id,
  input                                                                       grant_out_port_wise,

  input [N_PE - 1 : 0][interconnect_pkg::GLOBAL_MEM_PER_BANK_ADDR_L - 1 : 0]  st_bank_addrs,
  input [N_PE - 1 : 0][DATA_L - 1 : 0]                                        st_data,

  input [interconnect_pkg::GLOBAL_MEM_PER_BANK_ADDR_L - 1 : 0]                init_bank_addr,
  input                                                                       init_mem_vld,
  input                                                                       init_mem_wr_en,
  input [DATA_L - 1 : 0]                                                      init_mem_wr_data,

  output [interconnect_pkg::GLOBAL_MEM_PER_BANK_ADDR_L - 1 : 0]               mem_addr,
  output [DATA_L - 1 : 0]                                                     mem_wr_data,
  output                                                                      mem_wr_en,
  output                                                                      mem_rd_en
);

  logic [interconnect_pkg::GLOBAL_MEM_PER_BANK_ADDR_L - 1 : 0] mem_addr_pre;
  logic                                                        mem_wr_en_pre;
  logic                                                        mem_rd_en_pre;
  logic [DATA_L - 1 : 0]                                       mem_wr_data_pre;
//  logic [N_PE - 1 : 0]                                        st_gnt;


  logic                                         st_gnt;
  logic                                         ld_gnt;
  logic [$clog2(N_PE) -1: 0]                    granted_requester_bank_id;

  assign granted_requester_bank_id = granted_requester_id[$clog2(N_PE) -1: 0];
  assign st_gnt = granted_requester_id[$clog2(N_PE)] ? 0 : 1;
  assign ld_gnt = ~ st_gnt;
  //===========================================
  //      Combinational
  //===========================================
  always_comb begin
    mem_wr_data_pre = st_data[granted_requester_bank_id];
    if (init_mem_vld) begin
      mem_addr_pre = init_bank_addr;
      mem_wr_en_pre= init_mem_wr_en;
      mem_rd_en_pre= ~init_mem_wr_en;
      mem_wr_data_pre = init_mem_wr_data;
    end else if (st_gnt) begin
      mem_addr_pre = st_bank_addrs[granted_requester_bank_id];
      mem_wr_en_pre = 1;
      mem_rd_en_pre = 0;
    end else if (ld_gnt) begin // grant_out_port_wise is high for both st and ld grant. So st_gnt should be checked first.
      mem_addr_pre = ld_bank_addrs[granted_requester_bank_id];
      mem_wr_en_pre = 0;
      mem_rd_en_pre = 1;
    end else begin
      mem_addr_pre = ld_bank_addrs[granted_requester_bank_id];
      mem_wr_en_pre = 0;
      mem_rd_en_pre = 0;
    end
  end
  
  assign mem_wr_data = mem_wr_data_pre;
  assign mem_wr_en = mem_wr_en_pre;
  assign mem_rd_en = mem_rd_en_pre;
  assign mem_addr = mem_addr_pre;
endmodule

module interconnect_outgoing_datapath_init (
  input clk, rst,
  
  input [N_GLOBAL_MEM_BANKS - 1 : 0] [DATA_L - 1 : 0] mem_rd_data,

  input [$clog2(N_GLOBAL_MEM_BANKS) - 1 : 0]                   init_bank_id,
  input                                                        init_mem_vld,
  input                                                        init_mem_wr_en,
  output [DATA_L - 1 : 0]                                      init_mem_rd_data,
  output                                                       init_mem_rd_data_vld
);
  localparam DELAY = interconnect_pkg::GLOBAL_MEM_RD_LATENCY;
  logic [DELAY - 1 : 0] [$clog2(N_GLOBAL_MEM_BANKS) - 1 : 0] init_bank_id_delayed;
  logic [DELAY - 1 : 0] rd_en_delayed;
  logic rd_en;
  
  assign rd_en = init_mem_vld ? ~init_mem_wr_en : 1'b0;
  
  always_ff @(posedge clk or negedge rst) begin
    if (rst== RESET_STATE) begin
      init_bank_id_delayed <= '0;
      rd_en_delayed <= '0;
    end else begin
      init_bank_id_delayed[0] <= init_bank_id;
      rd_en_delayed[0] <= rd_en;
      for (integer i=1; i< DELAY ; i=i+1) begin
        init_bank_id_delayed [i] <= init_bank_id_delayed[i-1];
        rd_en_delayed [i] <= rd_en_delayed[i-1];
      end
    end
  end
  
  assign init_mem_rd_data = mem_rd_data[init_bank_id_delayed[DELAY - 1]];
  assign init_mem_rd_data_vld = rd_en_delayed[DELAY - 1];
  
endmodule

module interconnect_outgoing_datapath_per_pe (
  input clk, rst,

  input [$clog2(N_GLOBAL_MEM_BANKS) - 1 : 0]          ld_mem_bank_id,
  input                                               ld_gnt,

  input [N_GLOBAL_MEM_BANKS - 1 : 0] [DATA_L - 1 : 0] mem_rd_data,

  output [DATA_L - 1 : 0]                             ld_data,
  output                                              ld_data_vld
); 
  localparam DELAY = interconnect_pkg::GLOBAL_MEM_RD_LATENCY;
  logic [DELAY - 1 : 0] [$clog2(N_GLOBAL_MEM_BANKS) - 1 : 0] ld_mem_bank_id_delayed;
  logic [DELAY - 1 : 0] ld_gnt_delayed;
  
  always_ff @(posedge clk or negedge rst) begin
    if (rst== RESET_STATE) begin
      ld_mem_bank_id_delayed <= '0;
      ld_gnt_delayed <= '0;
    end else begin
      ld_mem_bank_id_delayed[0] <= ld_mem_bank_id;
      ld_gnt_delayed[0] <= ld_gnt;
      for (integer i=1; i< DELAY ; i=i+1) begin
        ld_mem_bank_id_delayed [i] <= ld_mem_bank_id_delayed[i-1];
        ld_gnt_delayed [i] <= ld_gnt_delayed[i-1];
      end
    end
  end

  assign ld_data = mem_rd_data[ld_mem_bank_id_delayed[DELAY-1]];
  assign ld_data_vld = ld_gnt_delayed[DELAY - 1];
endmodule



`endif //INTERCONNECT_DATAPATH_DEF
