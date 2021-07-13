//=======================================================================
// Created by         : KU Leuven
// Filename           : pe_func_unit_interface_flow_control_ld.sv
// Author             : Nimish Shah
// Created On         : 2019-12-09 11:44
// Last Modified      : 
// Update Count       : 2019-12-09 11:44
// Description        : 
//                      
//=======================================================================
                                                                                              
`ifndef PE_FUNC_UNIT_INTERFACE_FLOW_CONTROL_LD_DEF
  `define PE_FUNC_UNIT_INTERFACE_FLOW_CONTROL_LD_DEF

`include "common.sv"

module pe_func_unit_interface_flow_control_ld (
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
  
  logic func_unit_rdy_pre;

  assign func_unit_rdy_pre = ifc_en & memory_unit_rdy & instr_done;
  assign func_unit_rdy = func_unit_rdy_pre;
  assign ifc_unblocked = ~ifc_en | memory_unit_rdy;
  assign reg_en = func_unit_rdy_pre;

  assert property (@(posedge clk) if (!ifc_en) (ifc_unblocked)) else $warning("ifc cannot be blocked if not receive enable");
  assert property (@(posedge clk) if (!ifc_en) (!func_unit_rdy_pre)) else $warning("ifc cannot be blocked if not receive enable");

  assert property (@(posedge clk) func_unit_rdy_pre |-> ifc_unblocked) else $warning(1);
  assert property (@(posedge clk) func_unit_rdy_pre |-> memory_unit_rdy) else $warning(1);
  
endmodule


`endif //PE_FUNC_UNIT_INTERFACE_FLOW_CONTROL_LD_DEF
