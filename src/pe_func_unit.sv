//=======================================================================
// Created by         : KU Leuven
// Filename           : pe_func_unit.sv
// Author             : Nimish Shah
// Created On         : 2019-12-06 13:44
// Last Modified      : 
// Update Count       : 2019-12-06 13:44
// Description        : 
//                      
//=======================================================================

`ifndef PE_FUNC_UNIT_DEF
  `define PE_FUNC_UNIT_DEF

`include "common.sv"
`include "pe_operator.sv"
`include "pe_instr_decd.sv"
`include "pe_func_unit_interface_flow_control_ld.sv"
`include "pe_func_unit_interface_flow_control_st.sv"

//                     +---------------------------------------------------------------+                  
//                     |                                                               |                  
//                     |                                        ---------------+       |                  
//                     |                                        ^              |       |                  
//                     |                                        |              |       |                  
//                     |     +-----------------+                |              |       |                  
//                     |     |                 |        +---------------+      |---------------->  st data
//     instr     ----------->|  instr decoder  |        |               |      |       |           st req 
//     instr req       |     |                 |------> |    operator   |      |       |           st ack 
//     instr ack       |     |                 |        |               |      |       |                  
//                     |     +-----------------+        +---------------+      |       |                  
//                     |               -\                     ^    ^           |       |<------all stored 
//                     |                 -\                   |    |           |       |                  
//                     |                   -\                 |    |           |       |                  
//                     |                     --\              |    |           |       |                  
//                     |                        -\     +------------------+    |       |                  
//                     |                          -\   |                  |    |       |                  
//                     |                            -> |    registers     |    |       |                  
//                     |                               |                  |    |       |                  
//                     |                               +------------------+    |       |                  
// ld stream len <---- |                                    >    ^     ^       |       |                  
// ld stream len vld   |                                  -/     |     |       |       |                  
//                     |                                 /       |     |       |       |                  
//                     |                               -/        |     +--------       |                  
//                     |                             -/          |                     |                  
//                     |                            /            |                     |                  
//                     +---------------------------/-------------|---------------------+                  
//                        ^                      /               |                                        
//                        |                ld data 0         ld data 1                                    
//                        |                ld reg addr 0     ld reg addr 1                                
//                        |                ld vld 0          ld vld 1                                     
//                        v                ld rdy 0          ld rdy 1                                     
//       global barrier reached                                                                           
//       global barrier reached by others                                                                 
                                                                                                       

module pe_func_unit (
  input clk,
  input rst,

   input [INSTR_L - 1 : 0]    instr,
   input                      instr_req,
   output                     instr_ack,

   input [DATA_L - 1 : 0]     ld_0_data,
   input [REG_ADDR_L - 1 : 0] ld_0_addr,
   input                      ld_0_vld,
   output                     ld_0_rdy,

   input [DATA_L - 1 : 0]     ld_1_data,
   input [REG_ADDR_L - 1 : 0] ld_1_addr,
   input                      ld_1_vld,
   output                     ld_1_rdy,

   output [DATA_L - 1 : 0]    st_data,
   output                     st_req,
   input                      st_ack,

  output [pe_pkg::LD_STREAM_CNT_L - 1 : 0] ld_stream_len,
  output                                   ld_stream_len_vld,

  input  all_stored,

  output global_barrier_reached,
  input  global_barrier_reached_by_all_pes,

  input [PRECISION_CONFIG_L - 1 : 0] precision_config,

  // monitor
  input monitor,
  output [DATA_L - 1 : 0] monitor_pe_out,
  output [INSTR_L - 1 : 0] monitor_instr
); 

  import pe_pkg::*;

  //===========================================
  //      Signals 
  //===========================================
  logic [REGBANK_SIZE - 1 : 0] [DATA_L - 1 : 0] registers;
  logic [REGBANK_SIZE - 1 : 0] [DATA_L - 1 : 0] registers_d;

  logic [DATA_L - 1 : 0]                        reg_out_0;
  logic [REG_ADDR_L - 1 : 0]                    reg_rd_addr_0;
  logic [DATA_L - 1 : 0]                        reg_out_1;
  logic [REG_ADDR_L - 1 : 0]                    reg_rd_addr_1;
  logic reg_wr_0_en;
  logic reg_wr_1_en;
  
  logic [INSTR_L -1 : 0] instr_to_decd;
  logic [OPCODE_L - 1: 0] opcode;
  logic instr_ld_0_en;
  logic instr_ld_1_en;
  logic instr_st_en;


  // operator related
  logic operator_reg_wr_en;
  logic operator_reg_wr_en_ungated;
  logic [REG_ADDR_L - 1: 0] operator_reg_wr_addr;
  logic [DATA_L - 1 : 0]    operator_out;
  logic [DATA_L - 1 : 0]    operator_in_0;
  logic [DATA_L - 1 : 0]    operator_in_1;
  
                                                                                    

  // flow control related
  logic ld_0_rdy_pre;
  logic ld_1_rdy_pre;
  logic st_req_pre;
  
  logic instr_ack_pre;
  logic ld_0_unblocked;
  logic ld_1_unblocked;
  logic st_unblocked;
  logic local_barrier_unblocked;
  logic global_barrier_unblocked;

  logic global_barrier_reached_pre;
  logic local_barrier_reached;

  logic ld_stream_len_vld_pre;
  
  // statistics
  logic [32 : 0] barrier_stalls;
  logic [32 : 0] ld_stalls;
  logic [32 : 0] st_stalls;
  logic [32 : 0] active;

  //===========================================
  //      Instances 
  //===========================================
  pe_instr_decd PE_INSTR_DECD_INS (
    .instr               (instr_to_decd),
    .opcode              (opcode),
    .reg_rd_addr_0       (reg_rd_addr_0),
    .reg_rd_addr_1       (reg_rd_addr_1),
    .operator_reg_wr_addr(operator_reg_wr_addr),
    .ld_0_en             (instr_ld_0_en),
    .ld_1_en             (instr_ld_1_en),
    .st_en               (instr_st_en),
    .ld_stream_len       (ld_stream_len)

  );

  pe_func_unit_interface_flow_control_ld PE_FUNC_UNIT_INTERFACE_FLOW_CONTROL_LD_0_INS (
    .clk            (clk),
    .rst            (rst),
    .ifc_en         (instr_ld_0_en),
    
    .ifc_unblocked  (ld_0_unblocked),
    .instr_done     (instr_ack_pre),
    .reg_en         (reg_wr_0_en),

    .memory_unit_rdy(ld_0_vld),
    .func_unit_rdy  (ld_0_rdy)
  );

  pe_func_unit_interface_flow_control_ld PE_FUNC_UNIT_INTERFACE_FLOW_CONTROL_LD_1_INS (
    .clk            (clk),
    .rst            (rst),
    .ifc_en         (instr_ld_1_en),
    
    .ifc_unblocked  (ld_1_unblocked),
    .instr_done     (instr_ack_pre),
    .reg_en         (reg_wr_1_en),

    .memory_unit_rdy(ld_1_vld),
    .func_unit_rdy  (ld_1_rdy)
  );

  pe_func_unit_interface_flow_control_st PE_FUNC_UNIT_INTERFACE_FLOW_CONTROL_ST_INS(
    .clk            (clk),
    .rst            (rst),
    .ifc_en         (instr_st_en),

    .ifc_unblocked  (st_unblocked),
    .instr_done     (instr_ack_pre),
    .reg_en         (),

    .memory_unit_rdy(st_ack),
    .func_unit_rdy  (st_req)
  );
  
  pe_operator PE_OPERATOR_INS (
    .clk             (clk),
    .rst             (rst),
    .in_0            (operator_in_0),
    .in_1            (operator_in_1),
    .out             (operator_out),
    .opcode          (opcode),

    .precision_config(precision_config)
  );
  //===========================================
  //      Concurrent 
  //===========================================
  assign instr_to_decd = instr_req ? instr : '0;
  assign reg_out_0 = registers[reg_rd_addr_0];
  assign reg_out_1 = registers[reg_rd_addr_1];
  assign operator_in_0 = reg_out_0;
  assign operator_in_1 = reg_out_1;
  
  //===========================================
  //      Flow control 
  //===========================================
//  assign ld_0_unblocked = ld_0_rdy_pre ? ld_0_vld : 1;
//  assign ld_1_unblocked = ld_1_rdy_pre ? ld_1_vld : 1;
//  assign st_unblocked   = st_req_pre   ? st_ack : 1;
  assign local_barrier_unblocked  = local_barrier_reached      ? all_stored : 1;
  assign global_barrier_unblocked = global_barrier_reached_pre ? global_barrier_reached_by_all_pes : 1;

  always_comb begin
    instr_ack_pre = 0;
    if (instr_req) begin
      instr_ack_pre = ld_0_unblocked &
                      ld_1_unblocked &
                      st_unblocked &
                      local_barrier_unblocked &
                      global_barrier_unblocked;
    end
  end

  assign operator_reg_wr_en = operator_reg_wr_en_ungated & instr_ack_pre;


  //===========================================
  //       Combinational
  //===========================================

  always_comb begin
    operator_reg_wr_en_ungated= 0;
    local_barrier_reached = 0;
    global_barrier_reached_pre= 0;
    ld_stream_len_vld_pre= 0;
    case (opcode) 
      SUM_OPCODE : begin 
        operator_reg_wr_en_ungated = 1;
      end
      PROD_OPCODE : begin 
        operator_reg_wr_en_ungated = 1;
      end
      LOCAL_BARRIER_OPCODE: begin 
        local_barrier_reached = 1;
      end
      GLOBAL_BARRIER_OPCODE: begin 
        global_barrier_reached_pre = 1;
      end

      SET_LD_STREAM_LEN_OPCODE: begin
        ld_stream_len_vld_pre= 1;
      end
    endcase
  end

  //===========================================
  //      Sequential 
  //===========================================

  always_comb begin
    registers_d = registers;
    if (reg_wr_0_en) begin
      registers_d[ld_0_addr] = ld_0_data;
      assert(!$isunknown(ld_0_data)) else $warning("%h", ld_0_data);
      assert(!$isunknown(ld_0_addr)) else $warning("%h", ld_0_addr);
    end
    if (reg_wr_1_en) begin
      registers_d[ld_1_addr] = ld_1_data;
      assert(!$isunknown(ld_1_data)) else $warning("%h", ld_1_data);
      assert(!$isunknown(ld_1_addr)) else $warning("%h", ld_1_addr);
    end
    if (operator_reg_wr_en) begin
      registers_d[operator_reg_wr_addr] = operator_out;
      assert(!$isunknown(operator_out)) else $warning("%h", operator_out);
      assert(!$isunknown(operator_reg_wr_addr)) else $warning("%h", operator_reg_wr_addr);
    end
  end

  always_ff @(posedge clk or negedge rst) begin
    if (rst== RESET_STATE) begin
      registers <= '0;
    end else begin
      registers <= registers_d;
    end
  end

  //===========================================
  //       Outputs
  //===========================================
  assign st_data = operator_out;
  assign global_barrier_reached= global_barrier_reached_pre;
  assign ld_stream_len_vld= ld_stream_len_vld_pre;
  assign instr_ack = instr_ack_pre;

  //===========================================
  //       Assertions
  //===========================================

  assert property (@(posedge clk) if (local_barrier_reached )(!ld_0_vld)) else $warning("There shouldnot be valid data to load when local barrier has reached");
  assert property (@(posedge clk) if (local_barrier_reached )(!ld_1_vld)) else $warning("There shouldnot be valid data to load when local barrier has reached");
  assert property (@(posedge clk) if (global_barrier_reached) (!ld_0_vld)) else $warning("There shouldnot be valid data to load when barrier has reached");
  assert property (@(posedge clk) if (global_barrier_reached) (!ld_1_vld)) else $warning("There shouldnot be valid data to load when barrier has reached");
  assert property (@(posedge clk) if (global_barrier_reached) (!instr_ld_0_en)) else $warning("Improper instruction");
  assert property (@(posedge clk) if (global_barrier_reached) (!instr_ld_1_en)) else $warning("Improper instruction");
  assert property (@(posedge clk) if (global_barrier_reached) (!instr_st_en)) else $warning("Improper instruction");
  assert property (@(posedge clk) if (local_barrier_reached )(!instr_ld_0_en)) else $warning("Improper instruction");
  assert property (@(posedge clk) if (local_barrier_reached )(!instr_ld_1_en)) else $warning("Improper instruction");
  assert property (@(posedge clk) if (local_barrier_reached )(!instr_st_en)) else $warning("Improper instruction");

  assert property (@(posedge clk) if (ld_stream_len_vld_pre )(!instr_st_en)) else $warning("Improper instruction");
  assert property (@(posedge clk) if (ld_stream_len_vld_pre )(!instr_ld_0_en)) else $warning("Improper instruction");
  assert property (@(posedge clk) if (ld_stream_len_vld_pre )(!instr_ld_1_en)) else $warning("Improper instruction");
  

  always_ff @(posedge clk or negedge rst) begin
    if (rst== RESET_STATE) begin
      barrier_stalls <= 0;
      ld_stalls <= 0;
      st_stalls <= 0;
      active <= 0;
    end else begin
      if (global_barrier_reached_pre & ~global_barrier_reached_by_all_pes) begin
        barrier_stalls <= barrier_stalls + 1;
      end
      if (~ld_0_unblocked | ~ld_1_unblocked) begin
        ld_stalls <= ld_stalls + 1;
      end
      if (~st_unblocked) begin
        st_stalls <= st_stalls + 1;
      end
      if (instr_ack_pre) begin
        active <= active + 1;
      end
    end
  end

  always_ff @(posedge clk) begin
//    if (global_barrier_reached_pre & global_barrier_reached_by_all_pes) begin
//      $finish;
//    end
  end

  final begin
    $display("barrier_stalls : %d\n", barrier_stalls);
    $display("ld_stalls : %d\n", ld_stalls);
    $display("st_stalls : %d\n", st_stalls);
    $display("active : %d\n", active);
    $display("total : %d\n", active + st_stalls + ld_stalls + barrier_stalls);
  end

  always_ff @(posedge clk) begin
    case (opcode) 
      SUM_OPCODE : begin 
        assert (!global_barrier_reached_by_all_pes);
      end
      PROD_OPCODE : begin 
        assert (!global_barrier_reached_by_all_pes);
      end
      LOCAL_BARRIER_OPCODE: begin 
        assert (!ld_0_vld);
        assert (!ld_1_vld);
        assert (!st_ack);
        assert (!global_barrier_reached_by_all_pes);
      end
      GLOBAL_BARRIER_OPCODE: begin 
        assert (!ld_0_vld);
        assert (!ld_1_vld);
        assert (!st_ack);
      end

      SET_LD_STREAM_LEN_OPCODE: begin
        assert (!instr_ld_0_en);
        assert (!instr_ld_1_en);
        assert (!ld_0_vld);
        assert (!ld_1_vld);
        assert (!st_ack);
        assert (!global_barrier_reached_by_all_pes);
      end
    endcase
  end
  
  assign monitor_pe_out = monitor ? operator_out : '0;
  assign monitor_instr = monitor? instr_to_decd : '0;

endmodule

`endif //PE_FUNC_UNIT_DEF

