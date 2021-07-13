//=======================================================================
// Created by         : KU Leuven
// Filename           : pe_st_unit.sv
// Author             : Nimish Shah
// Created On         : 2019-12-05 14:39
// Last Modified      : 
// Update Count       : 2019-12-05 14:39
// Description        : 
//                      
//=======================================================================
`ifndef PE_ST_UNIT_DEF
  `define PE_ST_UNIT_DEF

//                                                                                          
//                                  fu st data                                              
//                                  fu st data req                                          
//                                  fu st data ack                                          
//                                       |                                                  
//                                       |                                                  
//                                       v                                                  
//                  +----------------------------------------------+                        
//                  |          /---------/                         |                        
//   local addr     |<---------         /                          |     st mem addr        
//   local data <---|<-----------------/-----------+---------------|<----st mem addr vld    
//   st req         |                 /            |               |     st mem addr rdy    
//   st ack         |                /             |               |                        
//                  |               v              |               |                        
//                  |         +-----------+  +-----v-----+         |                        
//                  |         |           |  |           |         |                        
//                  |         | global    |  | global    |         |                        
//                  |         | data fifo |  | addr fifo |         |                        
//                  |         |           |  |           |         |                        
//                  |         +-----------+  +-----------+         |                        
//                  |               |              |               |                        
//                  |               |              |               |                        
//                  |               v              v               |                        
//                  +----------------------------------------------+                        
//                                         |                                                
//                                         |                                                
//                                         v                                                
//                                   global addr                                            
//                                   global data                                            
//                                   global st req                                          
//                                   global st ack                                          
//                                                                                                


`include "common.sv"
`include "fifo.sv"

module pe_st_unit (
  input clk,
  input rst,

  // interface to mem addr stream
  input [GLOBAL_MEM_ADDR_L - 1 : 0] mem_addr_in,
  input                             mem_addr_in_req,
  output                            mem_addr_in_ack,

  // interface to global mem
  output [GLOBAL_MEM_ADDR_L - 1 : 0] global_mem_addr,
  output [DATA_L - 1 : 0]            global_mem_data,
  output                             global_mem_st_req,
  input                              global_mem_st_gnt,

  // interface to local mem
  output [LOCAL_MEM_ADDR_L - 1 : 0] local_mem_addr,
  output [DATA_L - 1 : 0]            local_mem_data,
  output                             local_mem_st_req,
  input                              local_mem_st_gnt,
  
  // from func unit
  input [DATA_L - 1 : 0] fu_st_data,
  input                  fu_st_data_req,
  output                 fu_st_data_gnt,

  output                 all_stored
); 

  //===========================================
  //       Signals
  //===========================================
  logic global_addr_fifo_out_vld;
  logic global_addr_fifo_in_rdy;

  logic global_data_fifo_in_rdy;
  logic global_data_fifo_in_vld;
  logic global_data_fifo_out_vld;

  logic fu_st_data_gnt_pre;

  logic st_unit_rdy_to_store;
  
  logic local_mem_addr_range;
  
  logic local_mem_st_req_pre;

  //===========================================
  //       Flow control
  //===========================================
  assign st_unit_rdy_to_store = mem_addr_in_req;
  assign local_mem_addr_range = (mem_addr_in[LOCAL_MEM_INDICATOR_S +: LOCAL_MEM_INDICATOR_L] == LOCAL_MEM_INDICATOR) ? 1 : 0;

  always_comb begin
    local_mem_st_req_pre = 0;
    if (local_mem_addr_range && st_unit_rdy_to_store) begin
      local_mem_st_req_pre = fu_st_data_req;
    end
  end

  always_comb begin
    global_data_fifo_in_vld = 0;
    if (~local_mem_addr_range && st_unit_rdy_to_store) begin
      global_data_fifo_in_vld = fu_st_data_req;
    end
  end

  always_comb begin
    fu_st_data_gnt_pre= 0;
    if (local_mem_addr_range) begin
      fu_st_data_gnt_pre = st_unit_rdy_to_store & fu_st_data_req & local_mem_st_gnt; // ANDing with req just for additional safety
    end else begin
      fu_st_data_gnt_pre = st_unit_rdy_to_store & fu_st_data_req & global_data_fifo_in_rdy; // ANDing with req just for additional safety
    end
  end
  //===========================================
  //       FIFOs
  //===========================================
  fifo #(.WORD_L(GLOBAL_MEM_ADDR_L), .DEPTH(pe_pkg::ST_DATA_FIFO_DEPTH), .PORT_L(1))
    GLOBAL_ADDR_FIFO (
      .clk            (clk),
      .rst            (rst),

      .inputs         (mem_addr_in),
      .in_vld         (global_data_fifo_in_vld),
      .fifo_rdy       (global_addr_fifo_in_rdy),

      .outputs        (global_mem_addr),
      .fifo_out_vld   (global_addr_fifo_out_vld),
      .receiver_rdy   (global_mem_st_gnt)
    );

  fifo #(.WORD_L(DATA_L), .DEPTH(pe_pkg::ST_DATA_FIFO_DEPTH), .PORT_L(1))
    GLOBAL_DATA_FIFO (
      .clk            (clk),
      .rst            (rst),

      .inputs         (fu_st_data),
      .in_vld         (global_data_fifo_in_vld),
      .fifo_rdy       (global_data_fifo_in_rdy),

      .outputs        (global_mem_data),
      .fifo_out_vld   (global_data_fifo_out_vld),
      .receiver_rdy   (global_mem_st_gnt)
    );
  
  //===========================================
  //       Outputs
  //===========================================
  assign all_stored       = ~global_data_fifo_out_vld;
  assign fu_st_data_gnt   = fu_st_data_gnt_pre;
  assign mem_addr_in_ack  = fu_st_data_gnt_pre;
  assign local_mem_addr   = mem_addr_in[LOCAL_MEM_ADDR_L -1 : 0];
  assign local_mem_data   = fu_st_data;
  assign local_mem_st_req = local_mem_st_req_pre;
  assign global_mem_st_req= global_data_fifo_out_vld;

  //===========================================
  //       Assertions
  //===========================================
  assert property (@(posedge clk) global_mem_st_req == global_addr_fifo_out_vld) else $warning("Data and addr fifo should be in sync");
  assert property (@(posedge clk) global_data_fifo_in_rdy == global_addr_fifo_in_rdy) else $warning("Data and addr fifo should be in sync");

  assert property (@(posedge clk) if (global_mem_st_gnt) (global_mem_st_req)) else $warning("Grant cannot be asserted without Request");
  assert property (@(posedge clk) if (local_mem_st_gnt) (local_mem_st_req)) else $warning(1);
  assert property (@(posedge clk) if (fu_st_data_gnt) (fu_st_data_req)) else $warning(1);

  //assert property (@(posedge clk) mem_addr_in_ack == fu_st_data_gnt) else $warning("Addr should be consumed along with data");
 

endmodule


`endif //PE_ST_UNIT_DEF
