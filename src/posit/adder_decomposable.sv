//=======================================================================
// Created by         : KU Leuven
// Filename           : adder_decomposable.sv
// Author             : Nimish Shah
// Created On         : 2019-12-22 15:25
// Last Modified      : 
// Update Count       : 2019-12-22 15:25
// Description        : 
//                      
//=======================================================================

`ifndef ADDER_DECOMPOSABLE_DEF
  `define ADDER_DECOMPOSABLE_DEF

  `include "../common.sv"
module adder_decomposable #(parameter EACH_ADDER_LEN= 8, N_ADDERS= 4) (
  input  unsigned [EACH_ADDER_LEN * N_ADDERS - 1 : 0] in0,
  input  unsigned [EACH_ADDER_LEN * N_ADDERS - 1 : 0] in1,
  input  unsigned [PRECISION_CONFIG_L - 1 : 0] mode,

  output unsigned  [N_ADDERS -1 : 0][EACH_ADDER_LEN : 0] out_quart,
  output unsigned  [1 : 0] [2*EACH_ADDER_LEN : 0]        out_half,
  output unsigned  [4* EACH_ADDER_LEN : 0]               out_full
); 
  localparam TOTAL_LEN= N_ADDERS * EACH_ADDER_LEN;

  logic unsigned [N_ADDERS -1 : 0][EACH_ADDER_LEN : 0] out_quart_pre;

  logic unsigned [N_ADDERS - 1 : 0] carry_out;
  logic unsigned [N_ADDERS - 1 : 0] carry_in;
  

  always_comb begin
    carry_in = 'x;
    carry_in[0] = 1'b0;

    for (integer i=1; i< N_ADDERS; i=i+1) begin
      carry_in[i] = carry_out[i-1];
    end

    if (mode == pe_pkg::PRECISION_CONFIG_16B) begin
      carry_in[2] = 0;
    end

    if (mode == pe_pkg::PRECISION_CONFIG_8B) begin
      for (integer i=1; i< N_ADDERS; i=i+1) begin
        carry_in[i] = 0;
      end
    end
  end

  generate
    genvar part_i;
    for (part_i=0; part_i<N_ADDERS; part_i=part_i+1) begin: part_loop
      adder_building_block #(.LEN(EACH_ADDER_LEN)) ADDER_BUILDING_BLOCK_INS (
        .in0 (in0[part_i*EACH_ADDER_LEN +: EACH_ADDER_LEN]),
        .in1 (in1[part_i*EACH_ADDER_LEN +: EACH_ADDER_LEN]),
        
        .carry_in (carry_in[part_i]),
        .out (out_quart_pre[part_i]),
        .carry_out (carry_out[part_i])
      );
    end
  endgenerate
  
  assign out_quart = out_quart_pre;

  assign out_half[0] = {out_quart_pre[1], out_quart_pre[0][EACH_ADDER_LEN - 1 : 0]};
  assign out_half[1] = {out_quart_pre[3], out_quart_pre[2][EACH_ADDER_LEN - 1 : 0]};
  
  assign out_full = {out_quart_pre[3][EACH_ADDER_LEN     : 0], out_quart_pre[2][EACH_ADDER_LEN - 1 : 0], 
                     out_quart_pre[1][EACH_ADDER_LEN - 1 : 0], out_quart_pre[0][EACH_ADDER_LEN - 1 : 0]};
endmodule

module adder_building_block #(parameter LEN= 8)(
  input [LEN - 1 : 0] in0,
  input [LEN - 1 : 0] in1,

  input carry_in,

  output [LEN : 0] out,
  output carry_out
); 
  
  logic [LEN : 0] out_pre;
  
  assign out_pre = in0 + in1 + carry_in;

  assign out = out_pre;
  assign carry_out = out_pre[LEN];
endmodule

`endif //ADDER_DECOMPOSABLE_DEF

