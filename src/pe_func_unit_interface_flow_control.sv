//=======================================================================
// Created by         : KU Leuven
// Filename           : pe_func_unit_interface_flow_control.sv
// Author             : Nimish Shah
// Created On         : 2019-12-09 11:44
// Last Modified      : 
// Update Count       : 2019-12-09 11:44
// Description        : 
//                      
//=======================================================================
                                                                                              

//===========================================
//       Block diagram
//===========================================
//                               to/from func unit flow control                                 
//                                                                                              
//                                                                                              
//                      ld 0 unblocked              this instr done       reg ld en             
//                                                                                              
//                             ^                         |                    ^                 
//                             |                         |                    |                 
//                             |                         v                    |                 
//                                                                                              
//               ~ld_0_en or done or data_vld                         ld_0_en & data_vld & ~done
//                                                                                              
//                                                       ld_0_en & data_vld & ~this instr done                     
//                                                       --------------->                       
//                                        +-------------+                 +-----------+         
// ld_0_en  ------->        done state    |    reset    |                 |   set     |         
//                          transition    +-------------+ <---------------+-----------+         
//                                                         this instr done                      
//                                                                                              
//                                                                                              
//                                                                                              
//                                    ld_0_en & ~done                                           
//                                                                                              
//                             ^           |                                                    
//                             |           |                                                    
//                             |           |                                                    
//                             |           v                                                    
//                         data_vld    func_unit_rdy                                                         
//                                                                                              
//                         to/from load 0 unit                                                  

`ifndef PE_FUNC_UNIT_INTERFACE_FLOW_CONTROL_DEF
  `define PE_FUNC_UNIT_INTERFACE_FLOW_CONTROL_DEF

`include "common.sv"

module pe_func_unit_interface_flow_control (
  input clk, 
  input rst,
  
  // to/from func unit parent flow control
  input  ifc_en,
  output ifc_unblocked,
  input  instr_done,
  output reg_en,

  // to/from ld/st units
  input  memory_unit_rdy,
  output func_unit_rdy
); 
  
  logic done;

  assign func_unit_rdy = ifc_en & ~done;
  assign ifc_unblocked = ~ifc_en | done | memory_unit_rdy;
  assign reg_en = ifc_en & memory_unit_rdy & ~done;


  always_ff @(posedge clk or negedge rst) begin
    if (rst== RESET_STATE) begin
      done <= 0;
    end else begin
      if (done == 0) begin
        if (ifc_en & memory_unit_rdy & ~instr_done) begin
          done <= 1;
        end
      end else begin // done == 1
        if (instr_done) begin
          done <= 0;
        end
      end
    end
  end

  assert property (@(posedge clk) if (!ifc_en) (ifc_unblocked)) else $warning("ifc cannot be blocked if not receive enable");
  assert property (@(posedge clk) if (!ifc_en) (!func_unit_rdy)) else $warning("ifc cannot be blocked if not receive enable");
  assert property (@(posedge clk) if (done) (!func_unit_rdy)) else $warning(1);
  assert property (@(posedge clk) if (done) (ifc_unblocked)) else $warning(1);
  
endmodule


`endif //PE_FUNC_UNIT_INTERFACE_FLOW_CONTROL_DEF
