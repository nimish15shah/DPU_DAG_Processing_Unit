//=======================================================================
// Created by         : KU Leuven
// Filename           : flt_multiplier.sv
// Author             : Nimish Shah
// Created On         : 2019-12-24 21:22
// Last Modified      : 
// Update Count       : 2019-12-24 21:22
// Description        : 
//                      
//=======================================================================

`ifndef FLT_MULTIPLIER_DECOMPOSABLE_DEF
  `define FLT_MULTIPLIER_DECOMPOSABLE_DEF

  `include "posit_pkg.sv"
  `include "multiplier_decomposable.sv"

module flt_multiplier_decomposable (
  input posit_pkg::exp_full_t         exp_full_in_0,
  input posit_pkg::mant_full_t       mant_full_in_0,

  input posit_pkg::exp_half_t   [1:0] exp_half_in_0,
  input posit_pkg::mant_half_t  [1:0] mant_half_in_0,
                                          
  input posit_pkg::exp_quart_t  [3:0] exp_quart_in_0,
  input posit_pkg::mant_quart_t [3:0] mant_quart_in_0,

  input posit_pkg::exp_full_t         exp_full_in_1,
  input posit_pkg::mant_full_t       mant_full_in_1,

  input posit_pkg::exp_half_t   [1:0] exp_half_in_1,
  input posit_pkg::mant_half_t  [1:0] mant_half_in_1,
                                          
  input posit_pkg::exp_quart_t  [3:0] exp_quart_in_1,
  input posit_pkg::mant_quart_t [3:0] mant_quart_in_1,

  input [PRECISION_CONFIG_L - 1 : 0] mode,

  output [posit_pkg::EXP_COMBINED_FULL_L : 0]        exp_full_out,
  output [1:0] [posit_pkg::EXP_COMBINED_HALF_L : 0]  exp_half_out,
  output [3:0] [posit_pkg::EXP_COMBINED_QUART_L : 0] exp_quart_out,

  output [posit_pkg::MANT_FULL_L + 1 : 0]            mant_full_out,
  output [1 : 0] [posit_pkg::MANT_HALF_L + 1 : 0]    mant_half_out,
  output [3 : 0] [posit_pkg::MANT_QUART_L + 1 : 0]   mant_quart_out
); 
  import posit_pkg::*;

  localparam MAX_EXP_FULL= 2**(EXP_COMBINED_FULL_L - 1) -1;  
  localparam MIN_EXP_FULL= -(2**(EXP_COMBINED_FULL_L -1));  

  localparam MAX_EXP_HALF= 2**(EXP_COMBINED_HALF_L - 1) -1;  
  localparam MIN_EXP_HALF= -(2**(EXP_COMBINED_HALF_L -1));  

  localparam MAX_EXP_QUART= 2**(EXP_COMBINED_QUART_L - 1) -1;  
  localparam MIN_EXP_QUART= -(2**(EXP_COMBINED_QUART_L -1));  

  logic [FULL_L - 1 : 0]       mul_in_0;
  logic [FULL_L - 1 : 0]       mul_in_1;
  logic [2*FULL_L - 1 : 0]     mul_out_full;
  logic [1:0][2*HALF_L -1 :0]  mul_out_half;
  logic [3:0][2*QUART_L -1 :0] mul_out_quart;
  
  // 1 bit extra than exp
  logic [EXP_COMBINED_FULL_L : 0]        res_exp_full ;
  logic [1:0] [EXP_COMBINED_HALF_L : 0]  res_exp_half ;
  logic [3:0] [EXP_COMBINED_QUART_L : 0] res_exp_quart;

  logic [posit_pkg::EXP_COMBINED_FULL_L : 0]        exp_full_out_pre;
  logic [1:0] [posit_pkg::EXP_COMBINED_HALF_L : 0]  exp_half_out_pre;
  logic [3:0] [posit_pkg::EXP_COMBINED_QUART_L : 0] exp_quart_out_pre;

  logic [posit_pkg::MANT_FULL_L + 1 : 0]            mant_full_out_pre;
  logic [1 : 0] [posit_pkg::MANT_HALF_L + 1 : 0]    mant_half_out_pre;
  logic [3 : 0] [posit_pkg::MANT_QUART_L + 1 : 0]   mant_quart_out_pre;

  assign res_exp_full = $signed(exp_full_in_0) + $signed(exp_full_in_1);
  always_comb begin
    foreach ( res_exp_half[i]) begin
      res_exp_half[i] = $signed(exp_half_in_0[i]) + $signed(exp_half_in_1[i]);
    end
  end
  always_comb begin
    foreach ( res_exp_quart[i]) begin
      res_exp_quart[i] = $signed(exp_quart_in_0[i]) + $signed(exp_quart_in_1[i]);
    end
  end

  // inputs of decomposable multiplier
  always_comb begin
    mul_in_0= '0;
    mul_in_1= '0;
    case (mode) 
      pe_pkg::PRECISION_CONFIG_32B : begin 
        mul_in_0 = mant_full_in_0;
        mul_in_1 = mant_full_in_1;
      end
      pe_pkg::PRECISION_CONFIG_16B : begin 
        foreach ( mant_half_in_0[i]) begin
          mul_in_0[i*HALF_L +: HALF_L] = mant_half_in_0[i];
          mul_in_1[i*HALF_L +: HALF_L] = mant_half_in_1[i];
        end
      end
      pe_pkg::PRECISION_CONFIG_8B : begin 
        foreach ( mant_quart_in_0[i]) begin
          mul_in_0[i*QUART_L +: QUART_L] = mant_quart_in_0[i];
          mul_in_1[i*QUART_L +: QUART_L] = mant_quart_in_1[i];
        end
      end
    endcase
  end
  
  // instantiate multipler
  multiplier_decomposable  #(.EACH_PART_LEN(QUART_L), .N_PARTS(4)) 
    MULTIPLIER_DECOMPOSABLE_INS (
      .in0        (mul_in_0),
      .in1        (mul_in_1),
      .mode       (mode),
      .out_full   (mul_out_full),
      .out_half   (mul_out_half),
      .out_quarter(mul_out_quart)
    ); 
  
  assign mant_full_out_pre= mul_out_full[2 * MANT_FULL_L - 1 -: (MANT_FULL_L + 2)];
  always_comb begin
    foreach ( mant_half_out_pre[i]) begin
      mant_half_out_pre[i] = mul_out_half[i][2 * MANT_HALF_L - 1 -: (MANT_HALF_L + 2)];
    end
  end
  always_comb begin
    foreach ( mant_quart_out_pre[i]) begin
      mant_quart_out_pre[i] = mul_out_quart[i][2 * MANT_QUART_L - 1 -: (MANT_QUART_L + 2)];
    end
  end

  assign exp_full_out  = res_exp_full  ;
  assign mant_full_out = mant_full_out_pre ;

  assign exp_half_out  = res_exp_half  ;
  assign mant_half_out = mant_half_out_pre ;

  assign exp_quart_out = res_exp_quart ;
  assign mant_quart_out= mant_quart_out_pre;

endmodule

`endif //FLT_MULTIPLIER_DECOMPOSABLE_DEF
