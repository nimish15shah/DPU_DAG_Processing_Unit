//=======================================================================
// Created by         : KU Leuven
// Filename           : pe_operator.sv
// Author             : Nimish Shah
// Created On         : 2019-12-06 16:09
// Last Modified      : 
// Update Count       : 2019-12-06 16:09
// Description        : 
//                      
//=======================================================================

`ifndef PE_OPERATOR_DEF
  `define PE_OPERATOR_DEF

`include "common.sv"  
//`include "module_library.sv"
`include "./posit/posit_arith_unit.sv"

module pe_operator (
  input clk, 
  input rst,
  input [DATA_L -1 : 0]    in_0,
  input [DATA_L -1 : 0]    in_1,
  output [DATA_L - 1 : 0]  out,

  input [OPCODE_L - 1 : 0] opcode,

  input [PRECISION_CONFIG_L - 1 : 0] precision_config
); 
  import pe_pkg::*;
  
  logic [DATA_L - 1 : 0] out_pre;
  logic [DATA_L - 1 : 0] sum_out;
  logic [DATA_L - 1 : 0] prod_out;
  logic mul_en;
  logic [DATA_L - 1 : 0] posit_out;

  logic [DATA_L -1 : 0]    in_0_gated;
  logic [DATA_L -1 : 0]    in_1_gated;
  
  logic in_0_bigger;

  assign in_0_bigger = $unsigned(in_0) > $unsigned(in_1) ? 1 : 0;

/*  
  flt_add #(.EXP_W(8), .MAN_W(DATA_L - 8)) 
    FLT_ADD_INS (
      .in1 (in_0),
      .in2 (in_1),
      .out (sum_out)
    );

  flt_mul #(.EXP_L(8), .MNT_L(DATA_L - 8)) 
    FLT_MUL_INS (
      .in1 (in_0),
      .in2 (in_1),
      .out (prod_out)
    );
*/
  posit_arith_unit POSIT_ARITH_UNIT_INS (
    .clk   (clk ), // for assertion
                
    .in_0  (in_0_gated),
    .in_1  (in_1_gated),
    .out   (posit_out),

    .mode  (precision_config),
    .mul_en // if 0 then add is enabled
  ); 

  always_comb begin
    mul_en = 0;
    in_0_gated = '0;
    in_1_gated = '0;
    out_pre = '0;

    case (opcode) 
      SUM_OPCODE: begin 
//        out_pre = in_0 + in_1;
//        out_pre= sum_out;
        in_0_gated = in_0;
        in_1_gated = in_1;
        out_pre = posit_out;
      end

      PROD_OPCODE: begin 
//        out_pre = in_0 * in_1;
//        out_pre= prod_out;
        in_0_gated = in_0;
        in_1_gated = in_1;
        out_pre = posit_out;
        mul_en= 1;
      end

      PASS_OPCODE: begin
        out_pre = in_0;
      end

      MAX_OPCODE: begin
        out_pre = in_0_bigger ? in_0 : in_1;
      end

      MIN_OPCODE: begin
        out_pre = in_0_bigger ? in_1 : in_0;
      end

      default : out_pre= '0;
    endcase
  end

  assign out = out_pre;
  
endmodule


`endif //PE_OPERATOR_DEF

