//=======================================================================
// Created by         : KU Leuven
// Filename           : interface.sv
// Author             : Nimish Shah
// Created On         : 2019-10-21 16:53
// Last Modified      : 
// Update Count       : 2019-10-21 16:53
// Description        : 
//                      
//=======================================================================
`ifndef INTERFACE_DEF
  `define INTERFACE_DEF

  `include "common.sv"

interface intf(input logic clk);
  logic rst;

  logic [periphery_pkg::INPUT_DATA_L -1 : 0] in;
  logic [periphery_pkg::IO_OPCODE_L - 1 : 0] io_opcode;

  logic reset_execution_io;
  logic enable_execution_io;
  logic  done_execution_io;

`ifdef DFT
  logic scan_en;
  logic dft_in;
  logic dft_out;
`endif
  logic  [31 : 0] out;

  // clocking block
  clocking cb @(posedge clk);
    default input#1.5ns output#5ns;
    output rst;
    output in;
    output io_opcode;
    output reset_execution_io;
    output enable_execution_io;

`ifdef DFT
    output scan_en;
    output dft_in;
    input dft_out;
`endif

    input done_execution_io;
    input out;
  endclocking

  modport tb_port (clocking cb); // synchronous TB

endinterface

`endif //INTERFACE_DEF
