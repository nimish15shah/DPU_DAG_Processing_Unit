//=======================================================================
// Created by         : KU Leuven
// Filename           : pe_ld_unit.sv
// Author             : Nimish Shah
// Created On         : 2019-12-04 13:33
// Last Modified      : 
// Update Count       : 2019-12-04 13:33
// Description        : 
//                      
//=======================================================================


//===========================================
//                                      +------------------+                                                              
//                                      |    reg banks     |                                                              
//                                      +------------------+                                                              
//                                                                                                                        
//                             reg_addr_out_0           reg_addr_out_1                                                    
//                             data_out_0               data_out_1                                                        
//                             data_out_0_vld           data_out_1_vld                                                    
//                             data_out_0_rdy           data_out_1_rdy                                                    
//                                                                                                                        
//                                    ^                       ^                                                           
//                                    |                       |                                                           
//                       +----------------------------------------------------+                                           
//                       |                                                    |                                           
//   ld_stream_len       |                                                    |                                           
//   ld_stream_len_vld-->|                                                    |                                           
//                       |                                                    |     local_mem_addr                        
//     reg_addr_in       |                                                    |---> local_mem_addr_req    +--------------+
//     mem_addr_in  ---->|                      pe_ld_unit                    |     local_mem_addr_gnt    |   local mem  |
// mem_addr_in_req       |                                                    |                           |              |
// mem_addr_in_ack       |                                                    | <-- local_mem_data        +--------------+
//                       |                                                    |     local_mem_data_rdy                    
//                       +----------------------------------------------------+                                           
//                                    |                        ^                                                          
//                                    v                        |                                                          
//                            global_mem_addr                                                                             
//                            global_mem_addr_req       global_mem_data                                                   
//                            global_mem_addr_gnt       global_mem_data_vld                                               
//                                                                                                                        
//                                        +-------------------+                                                           
//                                        |     global mem    |                                                           
//                                        +-------------------+                                                           
//===========================================

`ifndef PE_LD_UNIT_DEF
  `define PE_LD_UNIT_DEF

`include "common.sv"
`include "fifo.sv"

module pe_ld_unit (
  input clk, 
  input rst,
  
  // control interface
  input [pe_pkg::LD_STREAM_CNT_L - 1 : 0] ld_stream_len,
  input                                   ld_stream_len_vld,


  // interface to mem addr stream
  input [GLOBAL_MEM_ADDR_L - 1 : 0] mem_addr_in,
  input [REG_ADDR_L - 1: 0]         reg_addr_in,
  input                             mem_addr_in_req,
  output                            mem_addr_in_ack,
  
  // interface to global mem
  output [GLOBAL_MEM_ADDR_L- 1 : 0] global_mem_addr,
  output                            global_mem_addr_req,
  input                             global_mem_addr_gnt,

  input [DATA_L -1 : 0]             global_mem_data,
  input                             global_mem_data_vld,
  
  //local mem
  output [LOCAL_MEM_ADDR_L - 1 : 0] local_mem_addr,
  output                            local_mem_addr_req,
  input                             local_mem_addr_gnt,

  input [DATA_L -1 : 0]             local_mem_data,
  input                             local_mem_data_vld,
  
  // to func unit
  output [REG_ADDR_L - 1 : 0]       reg_addr_out_0,
  output [DATA_L - 1 : 0]           data_out_0,
  output                            data_out_0_vld,
  input                             data_out_0_rdy,

  output [REG_ADDR_L - 1 : 0]       reg_addr_out_1,
  output [DATA_L - 1 : 0]           data_out_1,
  output                            data_out_1_vld,
  input                             data_out_1_rdy
  
); 

  //===========================================
  //       Signals
  //===========================================
  // addr side
  logic [pe_pkg::LD_STREAM_CNT_L - 1 : 0] ld_counter;
  logic ld_counter_rdy;
  logic mem_addr_in_ack_pre;
  logic ld_unit_rdy_to_accept_addr;

  logic mem_type_fifo_rdy;
  logic reg_fifo_rdy;
  logic reg_out_0_vld;
  logic reg_out_1_vld;
  
  logic local_mem_addr_range;
  logic global_mem_addr_req_pre;
  logic local_mem_addr_req_pre;
  
  // data side
  logic [DATA_L - 1 : 0] data_fifo_in;
  logic data_fifo_in_vld;
  logic data_fifo_in_rdy;

  logic mem_type_fifo_out;
  logic mem_type_fifo_vld;

  logic pop_reg_fifo_0;
  logic pop_reg_fifo_1;
  
  //===========================================
  //       Flow control
  //===========================================
  
  // addr side flow control
  assign ld_counter_rdy = ld_counter != 0 ? 1 : 0;
  assign ld_unit_rdy_to_accept_addr = ld_counter_rdy & reg_fifo_rdy & mem_type_fifo_rdy;
  
  assign local_mem_addr_range = (mem_addr_in[LOCAL_MEM_INDICATOR_S +: LOCAL_MEM_INDICATOR_L] == LOCAL_MEM_INDICATOR) ? 1 : 0;
  
  assign pop_reg_fifo_0 = data_out_0_vld & data_out_0_rdy;
  assign pop_reg_fifo_1 = data_out_1_vld & data_out_1_rdy;

  always_comb begin
    global_mem_addr_req_pre = 0;
    local_mem_addr_req_pre = 0;
    if (ld_unit_rdy_to_accept_addr & mem_addr_in_req) begin
      if (local_mem_addr_range) begin
        local_mem_addr_req_pre= 1;
      end else begin
        global_mem_addr_req_pre= 1;
      end
    end
  end
  
  always_comb begin
    if (local_mem_addr_range) begin
      mem_addr_in_ack_pre = local_mem_addr_gnt & local_mem_addr_req_pre; // anding with req unnecessary, but just to make it future proof
    end else begin
      mem_addr_in_ack_pre = global_mem_addr_gnt & global_mem_addr_req_pre;
    end
  end

  // data side flow control
  assign data_fifo_in = mem_type_fifo_out ? local_mem_data : global_mem_data;

  always_comb begin
    data_fifo_in_vld = 0;
    
    if (mem_type_fifo_out) begin // local mem
      if (local_mem_data_vld) begin
        data_fifo_in_vld = 1;
      end
    end else begin // global mem
      if (global_mem_data_vld) begin
        data_fifo_in_vld = 1;
      end
    end
  end


  //===========================================
  //       FIFOs
  //===========================================
  // fifo to store data
  fifo_2out #(.WORD_L(DATA_L), .DEPTH(pe_pkg::LD_DATA_FIFO_DEPTH), .PORT_L(1))
    DATA_FIFO (
      .clk            (clk),
      .rst            (rst),

      .inputs         (data_fifo_in),
      .in_vld         (data_fifo_in_vld),
      .fifo_rdy       (data_fifo_in_rdy),

      .outputs_0      (data_out_0),
      .outputs_1      (data_out_1),
      .fifo_out_0_vld (data_out_0_vld),
      .fifo_out_1_vld (data_out_1_vld),
      .receiver_0_rdy (data_out_0_rdy),
      .receiver_1_rdy (data_out_1_rdy)
    );

  // fifo to store reg addr
  fifo_2out #(.WORD_L(REG_ADDR_L), .DEPTH(pe_pkg::LD_DATA_FIFO_DEPTH), .PORT_L(1))
    REG_ADDR_FIFO (
      .clk            (clk),
      .rst            (rst),

      .inputs         (reg_addr_in),
      .in_vld         (mem_addr_in_ack_pre),
      .fifo_rdy       (reg_fifo_rdy),

      .outputs_0      (reg_addr_out_0),
      .outputs_1      (reg_addr_out_1),
      .fifo_out_0_vld (reg_out_0_vld),
      .fifo_out_1_vld (reg_out_1_vld),
      .receiver_0_rdy (pop_reg_fifo_0),
      .receiver_1_rdy (pop_reg_fifo_1)
    );
  
  // fifo to store the type of memory req, 
  // which helps in putting data in order in data fifo
  fifo #(.WORD_L(1), .DEPTH(pe_pkg::MAX_OUTSTANDING_LD_REQ), .PORT_L(1))
    MEM_TYPE_FIFO (
      .clk            (clk),
      .rst            (rst),

      .inputs         (local_mem_addr_range),
      .in_vld         (mem_addr_in_ack_pre),
      .fifo_rdy       (mem_type_fifo_rdy),

      .outputs        (mem_type_fifo_out),
      .fifo_out_vld   (mem_type_fifo_vld),
      .receiver_rdy   (data_fifo_in_vld)
    );


  //===========================================
  //       Sequential
  //===========================================
  always_ff @(posedge clk or negedge rst) begin
    if (rst== RESET_STATE) begin
      ld_counter <= '0;
    end else begin
      if (ld_stream_len_vld) begin
        assert (ld_counter == 0) else $warning(1);
        ld_counter <= ld_stream_len;
      end else begin
        if (mem_addr_in_ack_pre) begin
          assert (ld_counter != 0) else $warning(1);
          ld_counter <= ld_counter - 1;
        end
      end
    end
  end

  //===========================================
  //       Outputs
  //===========================================
  assign mem_addr_in_ack = mem_addr_in_ack_pre;

  assign global_mem_addr = mem_addr_in;
  assign global_mem_addr_req = global_mem_addr_req_pre;

  assign local_mem_addr = mem_addr_in;
  assign local_mem_addr_req = local_mem_addr_req_pre;


  //===========================================
  //       Assertions
  //===========================================
  assert property (@(posedge clk) if (data_out_0_vld) (reg_out_0_vld)) else $warning("Data can only be valid if reg addr is already there");
  assert property (@(posedge clk) if (data_out_1_vld) (reg_out_1_vld)) else $warning(1);
  assert property (@(posedge clk) if (pop_reg_fifo_0) (reg_out_0_vld)) else $warning(1);
  assert property (@(posedge clk) if (pop_reg_fifo_1) (reg_out_1_vld)) else $warning(1);

  assert property (@(posedge clk) if (local_mem_data_vld | global_mem_data_vld) (mem_type_fifo_vld)) else $warning("Cannot recieve a data from mem, if not requested");
  assert property (@(posedge clk) if (local_mem_data_vld | global_mem_data_vld) (data_fifo_in_rdy == 1)) else $warning("Data fifo must have free space");
        
  assert property (@(posedge clk) reg_fifo_rdy |-> data_fifo_in_rdy) else $warning(1);
  assert property (@(posedge clk) (~reg_fifo_rdy & data_fifo_in_rdy) |-> mem_type_fifo_vld) else $warning(1);
  assert property (@(posedge clk) local_mem_data_vld |-> ~global_mem_data_vld) else $warning(1);
  assert property (@(posedge clk) global_mem_data_vld |-> ~local_mem_data_vld) else $warning(1);


  assert property (@(posedge clk) mem_addr_in_ack_pre |-> reg_fifo_rdy) else $warning(1);
  assert property (@(posedge clk) mem_addr_in_ack_pre |-> mem_type_fifo_rdy) else $warning(1);
  
  // ld latency assertions
  assert property (@(posedge clk) global_mem_addr_gnt |=> global_mem_data_vld) else $warning(1);
  assert property (@(posedge clk) local_mem_addr_gnt  |=> local_mem_data_vld) else $warning(1);

  // gnt should come within N_PE cycles of req
  assert property ( @(posedge clk) (global_mem_addr_req |-> ##[0:N_PE + 10] global_mem_addr_gnt)) else
    $error ("ack did not occur within 100 cycles after req");
  assert property ( @(posedge clk) (local_mem_addr_req |-> ##[0:N_PE + 10] local_mem_addr_gnt)) else
    $error ("ack did not occur within 100 cycles after req");
  
endmodule

`endif //PE_LD_UNIT_DEF
