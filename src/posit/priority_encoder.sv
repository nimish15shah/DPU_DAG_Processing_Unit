//=======================================================================
// Created by         : KU Leuven
// Filename           : priority_encoder.sv
// Author             : Nimish Shah
// Created On         : 2019-12-20 16:30
// Last Modified      : 
// Update Count       : 2019-12-20 16:30
// Description        : 
//                      
//=======================================================================

`ifndef PRIORITY_ENODER_DEF
  `define PRIORITY_ENODER_DEF

module priority_encoder_active_high #(parameter N_IN= 8) (
  input [N_IN - 1 : 0] in,
  output [$clog2(N_IN) - 1 : 0] out,

  output all_zeroes
); 
  // Active high. Finds the location of first 1
  // MSB given highest priority

  logic [$clog2(N_IN) - 1 : 0] out_pre;
  logic all_zeroes_pre;

  always_comb begin
    out_pre = 'x; // output set to x if there is no 1 in the inputs
    all_zeroes_pre = 1;
    for (integer i=0; i< N_IN; i=i+1) begin
      if (in[i] == 1) begin
        all_zeroes_pre = 0;
        out_pre = i;
      end
    end
  end
  assign all_zeroes = all_zeroes_pre;
  assign out= out_pre;

endmodule

module priority_encoder_active_low #(parameter N_IN= 8) (
  input [N_IN - 1 : 0] in,
  output [$clog2(N_IN) - 1 : 0] out,

  output all_ones
); 
  // Active low. Finds the location of first 0
  // MSB given highest priority

  // out is 'x if all_ones high

  logic [$clog2(N_IN) - 1 : 0] out_pre;
  logic all_ones_pre;

  always_comb begin
    out_pre = 'x; // output set to x if there is no 1 in the inputs
    all_ones_pre = 1;
    for (integer i=0; i< N_IN; i=i+1) begin
      if (in[i] == 0) begin
        all_ones_pre = 0;
        out_pre = i;
      end
    end
  end
  assign all_ones = all_ones_pre;
  assign out= out_pre;
endmodule



`endif //PRIORITY_ENODER_DEF
