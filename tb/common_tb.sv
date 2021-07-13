//=======================================================================
// Created by         : KU Leuven
// Filename           : common.sv
// Author             : Nimish Shah
// Created On         : 2019-10-21 16:54
// Last Modified      : 
// Update Count       : 2019-10-21 16:54
// Description        : 
//                      
//=======================================================================
`ifndef COMMON_TB_DEF
  `define COMMON_TB_DEF
  
/* `define GATE_NETLIST // Uncomment this for simulating gate-level netlist */

//`include "uvm_macros.svh"

`define VERIFICATION

`include "common.sv"

  // Include DUT files
`ifdef GATE_NETLIST
 // Path to STD CELL libraries and memory model
 // Path to the gate netlist
`else
  `include "pru_async_top.sv"
`endif

  // Common parameters, typedefs, enums
package common_types_params;
endpackage

`endif //COMMON_TB_DEF

