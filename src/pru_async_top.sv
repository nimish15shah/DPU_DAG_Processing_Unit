//=======================================================================
// Created by         : KU Leuven
// Filename           : pru_async_top.sv
// Author             : Nimish Shah
// Created On         : 2020-01-08 16:57
// Last Modified      : 
// Update Count       : 2020-01-08 16:57
// Description        : 
//                      
//=======================================================================

`ifndef PRU_ASYNC_TOP_DEF
  `define PRU_ASYNC_TOP_DEF
  
  `include "pru_async_wo_io.sv"
  `include "io_wrapper.sv"

module pru_async_top (
  input clk,
  input rst,

  input [periphery_pkg::INPUT_DATA_L - 1 : 0] in,
  input [periphery_pkg::IO_OPCODE_L -1 : 0] io_opcode,
  
  input reset_execution_io,
  input enable_execution_io,
  output done_execution_io,

`ifdef DFT
  input scan_en,
  input dft_in, 
  output dft_out,
`endif

  output [periphery_pkg::OUTPUT_DATA_L - 1 : 0] out
); 
  
  logic clk_core;
  logic rst_core;

  logic [periphery_pkg::INPUT_DATA_L -1 : 0] in_core;
  logic [periphery_pkg::IO_OPCODE_L -1 : 0] io_opcode_core;

  logic reset_execution_io_core;
  logic enable_execution_io_core;
  logic done_execution_io_core;

  logic [periphery_pkg::OUTPUT_DATA_L -1 : 0] out_core;

  pru_async_wo_io PRU_ASYNC_WO_IO_INS (
    .clk                 (clk_core),
    .rst                 (rst_core),
                                             
    .in                  (in_core),
    .io_opcode           (io_opcode_core),
                                             
    .reset_execution_io  (reset_execution_io_core),
    .enable_execution_io (enable_execution_io_core),
    .done_execution_io   (done_execution_io_core),

    .out (out_core)
  );

  io_wrapper IO_WRAPPER_INS (
    .clk_pad                  (clk                 ),
    .rst_pad                  (rst                 ),
    .in_pad                   (in                  ),
    .io_opcode_pad            (io_opcode),
    .reset_execution_io_pad   (reset_execution_io  ),
    .enable_execution_io_pad  (enable_execution_io ),
    .done_execution_io_pad    (done_execution_io   ),
    .out_pad                  (out),

    .clk_core                 (clk_core                 ),
    .rst_core                 (rst_core                 ),
    .in_core                  (in_core                  ),
    .io_opcode_core           (io_opcode_core),
    .reset_execution_io_core  (reset_execution_io_core  ),
    .enable_execution_io_core (enable_execution_io_core ),
    .done_execution_io_core   (done_execution_io_core   ),
    .out_core (out_core)
  );


endmodule


`endif //PRU_ASYNC_TOP_DEF
