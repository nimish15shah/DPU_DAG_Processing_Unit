//=======================================================================
// Created by         : KU Leuven
// Filename           : io_wrapper.sv
// Author             : Nimish Shah
// Created On         : 2020-01-17 16:30
// Last Modified      : 
// Update Count       : 2020-01-17 16:30
// Description        : 
//                      
//=======================================================================

`ifndef IO_WRAPPER_DEF
  `define IO_WRAPPER_DEF
module io_wrapper (
  // pad side
  input clk_pad,
  input rst_pad,

  input [periphery_pkg::INPUT_DATA_L- 1 : 0] in_pad,
  input [periphery_pkg::IO_OPCODE_L -1 : 0] io_opcode_pad,

  input reset_execution_io_pad,
  input enable_execution_io_pad,
  output done_execution_io_pad,

  output [periphery_pkg::OUTPUT_DATA_L - 1 : 0] out_pad,
  
  // core side
  output clk_core,
  output rst_core,

  output [periphery_pkg::INPUT_DATA_L - 1 : 0] in_core,
  output [periphery_pkg::IO_OPCODE_L -1 : 0] io_opcode_core,

  output reset_execution_io_core,
  output enable_execution_io_core,
  input done_execution_io_core,

  input [periphery_pkg::OUTPUT_DATA_L - 1 : 0] out_core
); 
  // clk
  // using regular IO cell, there is no special IO for clk
  PDDW08SDGZ_V_G io_clk (
    .I   (1'b0),
    .OEN (1'b1),
    .REN (1'b0),
    .PAD (clk_pad),
    .C   (clk_core)
  );


// naming convention
// P- nothing
// D- Without slew rate
// DW- pull down
// 08- drive strength in mA
// S- Schmitt trigger
// DGZ- Fail safe
// H- horizontal orientation
// G- nothing

// pin convention
// OEN: output enable (active low)
// REN: pull doen enable (active low)
// I -> PAD (output mode)
// PAD -> C (input mode)

  // Inputs
  PDDW08SDGZ_V_G io_rst (
    .I   (1'b0),
    .OEN (1'b1),
    .REN (1'b0),
    .PAD (rst_pad),
    .C   (rst_core)
  );

  PDDW08SDGZ_V_G io_reset_execution_io (
    .I   (1'b0),
    .OEN (1'b1),
    .REN (1'b0),
    .PAD (reset_execution_io_pad),
    .C   (reset_execution_io_core)
  );

  PDDW08SDGZ_V_G io_enable_execution_io (
    .I   (1'b0),
    .OEN (1'b1),
    .REN (1'b0),
    .PAD (enable_execution_io_pad),
    .C   (enable_execution_io_core)
  );

  generate
    genvar io_i_opcode;
    for (io_i_opcode=0; io_i_opcode< periphery_pkg::IO_OPCODE_L; io_i_opcode=io_i_opcode+1) begin: opcode_loop
      PDDW08SDGZ_V_G io_opcode (
        .I   (1'b0),
        .OEN (1'b1),
        .REN (1'b0),
        .PAD (io_opcode_pad[io_i_opcode]),
        .C   (io_opcode_core[io_i_opcode])
      );

    end
  endgenerate

  generate
    genvar io_i_in;
    for (io_i_in=0; io_i_in< periphery_pkg::INPUT_DATA_L; io_i_in=io_i_in+1) begin: in_loop
      PDDW08SDGZ_H_G io_in (
        .I   (1'b0),
        .OEN (1'b1),
        .REN (1'b0),
        .PAD (in_pad[io_i_in]),
        .C   (in_core[io_i_in])
      );

    end
  endgenerate

  // outputs
  PDDW08SDGZ_V_G io_done_execution_io (
    .I   (done_execution_io_core),
    .OEN (1'b0),
    .REN (1'b1), // pull down disabled
    .PAD (done_execution_io_pad),
    .C   ()
  );

  generate
    genvar io_i;
    for (io_i=0; io_i< periphery_pkg::OUTPUT_DATA_L; io_i=io_i+1) begin: out_loop

      if (io_i < periphery_pkg::OUTPUT_DATA_L/2) begin
        PDDW08SDGZ_H_G io_out (
          .I   (out_core[io_i]),
          .OEN (1'b0),
          .REN (1'b1), // pull down disabled
          .PAD (out_pad[io_i]),
          .C   ()
        );
      end else begin
        PDDW08SDGZ_V_G io_out (
          .I   (out_core[io_i]),
          .OEN (1'b0),
          .REN (1'b1), // pull down disabled
          .PAD (out_pad[io_i]),
          .C   ()
        );
      end
    end
  endgenerate

endmodule

`endif //IO_WRAPPER_DEF
