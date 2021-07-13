//=======================================================================
// Created by         : KU Leuven
// Filename           : flow_control_utils.sv
// Author             : Nimish Shah
// Created On         : 2020-01-07 21:38
// Last Modified      : 
// Update Count       : 2020-01-07 21:38
// Description        : 
//                      
//=======================================================================

`ifndef FLOW_CONTROL_UTILS_DEF
  `define FLOW_CONTROL_UTILS_DEF

module flow_control_vld_rdy_with_latency #(parameter LATENCY= 1) (
  input clk,
  input rst,

  input en,
  input flush,
  input reset_state,
  input rdy,

  output do_operation,
  output vld

);
//    +-----------------------------------------------------------------------------------+
//    |                                                               this module         |
//    |     en & rdy ------->----------+---------+                                        |
//    |                     |          |         |                                        |
//    |                     v          v         v                                        |
//    |                   +---+      +---+     +---+                                      |
//    |                   |   |      |   |     |   |                                      |
//    |                   |   |      |   |     |   |  pre_vld                             |
//    |                   |   |      |   |     |   |           +---------+                |
//    | do_operation----> |   |----> |   |---->|   |---------->|         |                |
//    |       |           |   |      |   |     |   |        -->|and gate |---------->     |
//    |       |           |   |      |   |     |   |     --/   |         |           vld  |
//    |       |           +---+      +---+     +---+   en      +---------+                |
//    +-------|---------------------------------------------------------------------------+
//            |      ------>----------+---------+                                          
//            |            |          |         |                                          
//            |            v          v         v                           <------- rdy   
//            v          +---+      +---+     +---+                                        
//       +----------+    |   |      |   |     |   |                                        
//       |          |    |   |      |   |     |   |                                        
//       |operation |    |   |      |   |     |   |                                        
//       |          |---->   |----> |   |---->|   |                                        
//       |          |    |   |      |   |     |   |                                        
//       +----------+    |   |      |   |     |   |                                        
//                       +---+      +---+     +---+                                        
//

  logic pre_vld;
  logic final_vld_pre;

  logic do_operation_pre;

  logic vld_rdy_unblocked;
  
  logic [LATENCY -1 : 0] do_operation_delayed;
  
  assign pre_vld = do_operation_delayed[LATENCY - 1];
  
  assign vld_rdy_unblocked = final_vld_pre ? rdy : 1'b1;

  always_comb begin
    do_operation_pre= 1'b0;
    if (en) begin
      do_operation_pre = vld_rdy_unblocked;
    end 
    if (flush) begin
      do_operation_pre = 1'b0;
    end
  end


  always_ff @(posedge clk or negedge rst) begin
    if (rst== RESET_STATE) begin
      do_operation_delayed <= '0;
    end else begin
      if (reset_state) begin
        do_operation_delayed <= '0;
      end else begin
        if ((en | flush) & vld_rdy_unblocked) begin
          do_operation_delayed[0] <= do_operation_pre;
          for (integer i=1; i< LATENCY ; i=i+1) begin
            do_operation_delayed [i] <= do_operation_delayed[i-1];
          end
        end
      end
    end
  end
  
  assign final_vld_pre = pre_vld & (en | flush);
  assign vld = final_vld_pre;
  assign do_operation = do_operation_pre;
  
  initial assert (LATENCY > 0);
endmodule


`endif //FLOW_CONTROL_UTILS_DEF
