//=======================================================================
// Created by         : KU Leuven
// Filename           : io_registers.sv
// Author             : Nimish Shah
// Created On         : 2020-02-26 16:52
// Last Modified      : 
// Update Count       : 2020-02-26 16:52
// Description        : 
//                      
//=======================================================================

`ifndef IO_REGISTERS_DEF
  `define IO_REGISTERS_DEF
  `include "common.sv"
module io_registers (
  input clk,
  input rst,

  input [periphery_pkg::INPUT_DATA_L - 1 : 0] in,
  input shift_en,

  output [periphery_pkg::INPUT_REG_L - 1 : 0] reg_data
); 
  import periphery_pkg::*;

  localparam MULTIPLE_FACTOR =  INPUT_REG_L / INPUT_DATA_L;
 

  logic [periphery_pkg::INPUT_REG_L - 1 : 0] reg_data_q;

  always_ff @(posedge clk or negedge rst) begin
    if (rst== RESET_STATE) begin
      reg_data_q <= '0;
    end else begin
      if (shift_en) begin
        reg_data_q[0 +: INPUT_DATA_L] <= in;
        for (integer i=1; i< MULTIPLE_FACTOR ; i=i+1) begin
          reg_data_q[i*INPUT_DATA_L +: INPUT_DATA_L] <= reg_data_q[(i-1)*INPUT_DATA_L +: INPUT_DATA_L];
        end
      end
    end
  end
  
  assign reg_data = reg_data_q;

endmodule


`endif //IO_REGISTERS_DEF
