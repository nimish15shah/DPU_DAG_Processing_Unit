//=======================================================================
// Created by         : KU Leuven
// Filename           : flt_adder.sv
// Author             : Nimish Shah
// Created On         : 2019-12-24 21:17
// Last Modified      : 
// Update Count       : 2019-12-24 21:17
// Description        : 
//                      
//=======================================================================

`ifndef FLT_ADDER_DECOMPOSABLE_DEF
  `define FLT_ADDER_DECOMPOSABLE_DEF

  `include "posit_pkg.sv"
  `include "shifter_decomposable.sv"
  `include "adder_decomposable.sv"
  `include "round_norm_overflow_underflow.sv"

module flt_adder_decomposable (
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
  
  localparam MAX_SHIFT_FULL= FULL_L - 1;
  localparam MAX_SHIFT_HALF= HALF_L - 1;
  localparam MAX_SHIFT_QUART= QUART_L - 1;

  logic [FULL_L - 1 : 0] adder_in_0;
  logic [FULL_L - 1 : 0] adder_in_1_pre_shift;
  logic [FULL_L - 1 : 0] adder_in_1_post_shift;
  logic [FULL_L : 0] adder_out_full;
  logic [1:0][HALF_L : 0] adder_out_half;
  logic [3:0][QUART_L : 0] adder_out_quart;

  logic [EXP_COMBINED_FULL_L : 0]        exp_full_diff,  bigger_exp_full;
  logic [1:0] [EXP_COMBINED_HALF_L : 0]  exp_half_diff,  bigger_exp_half;
  logic [3:0] [EXP_COMBINED_QUART_L : 0] exp_quart_diff, bigger_exp_quart;

  logic [3:0] [$clog2(FULL_L) - 1 :0] shift_val;

  logic [MANT_FULL_L + 1 : 0] adder_mant_out_full;
  logic [1 : 0] [MANT_HALF_L + 1 : 0] adder_mant_out_half;
  logic [3 : 0] [MANT_QUART_L + 1 : 0] adder_mant_out_quart;

  logic [posit_pkg::EXP_COMBINED_FULL_L : 0]        exp_full_out_pre;
  logic [1:0] [posit_pkg::EXP_COMBINED_HALF_L : 0]  exp_half_out_pre;
  logic [3:0] [posit_pkg::EXP_COMBINED_QUART_L : 0] exp_quart_out_pre;

  logic [posit_pkg::MANT_FULL_L + 1 : 0]            mant_full_out_pre;
  logic [1 : 0] [posit_pkg::MANT_HALF_L + 1 : 0]    mant_half_out_pre;
  logic [3 : 0] [posit_pkg::MANT_QUART_L + 1 : 0]   mant_quart_out_pre;

  always_comb begin
    adder_in_0 = '0;
    adder_in_1_pre_shift= '0;
    exp_full_diff= 'x;
    exp_half_diff= 'x;
    exp_quart_diff= 'x;
    bigger_exp_full= 'x;
    bigger_exp_half= 'x;
    bigger_exp_quart= 'x;
    
    // LSB of adder_in_0 and adder_in_1_pre_shift set to 0
    // Bits from [1 +: MANT_X_L] set to incoming mantissa.
    // LSB will be used for rounding
    case (mode) 
      pe_pkg::PRECISION_CONFIG_32B : begin 
        if ($signed(exp_full_in_0) > $signed(exp_full_in_1)) begin
          exp_full_diff = $signed(exp_full_in_0) - $signed(exp_full_in_1);
          adder_in_0[1 +: MANT_FULL_L] = mant_full_in_0;
          adder_in_1_pre_shift[1 +: MANT_FULL_L] = mant_full_in_1;
          bigger_exp_full= $signed(exp_full_in_0);
        end else begin
          exp_full_diff = $signed(exp_full_in_1) - $signed(exp_full_in_0);
          adder_in_0[1 +: MANT_FULL_L] = mant_full_in_1;
          adder_in_1_pre_shift[1 +: MANT_FULL_L] = mant_full_in_0;
          bigger_exp_full= $signed(exp_full_in_1);
        end
      end
      pe_pkg::PRECISION_CONFIG_16B : begin 
        foreach ( exp_half_diff[i]) begin
          if ($signed(exp_half_in_0[i]) > $signed(exp_half_in_1[i])) begin
            exp_half_diff[i] = $signed(exp_half_in_0[i]) - $signed(exp_half_in_1[i]);
            adder_in_0[i*HALF_L + 1 +: MANT_HALF_L] = mant_half_in_0[i];
            adder_in_1_pre_shift[i*HALF_L + 1 +: MANT_HALF_L] = mant_half_in_1[i];
            bigger_exp_half[i]= $signed(exp_half_in_0[i]);
          end else begin
            exp_half_diff[i] = $signed(exp_half_in_1[i]) - $signed(exp_half_in_0[i]);
            adder_in_0[i*HALF_L + 1 +: MANT_HALF_L] = mant_half_in_1[i];
            adder_in_1_pre_shift[i*HALF_L + 1 +: MANT_HALF_L] = mant_half_in_0[i];
            bigger_exp_half[i]= $signed(exp_half_in_1[i]);
          end
        end
      end
      pe_pkg::PRECISION_CONFIG_8B : begin 
        foreach ( exp_quart_diff[i]) begin
          if ($signed(exp_quart_in_0[i]) > $signed(exp_quart_in_1[i])) begin
            exp_quart_diff[i] = $signed(exp_quart_in_0[i]) - $signed(exp_quart_in_1[i]);
            adder_in_0[i*QUART_L + 1 +: MANT_QUART_L] = mant_quart_in_0[i];
            adder_in_1_pre_shift[i*QUART_L + 1 +: MANT_QUART_L] = mant_quart_in_1[i];
            bigger_exp_quart[i]= $signed(exp_quart_in_0[i]);
          end else begin
            exp_quart_diff[i] = $signed(exp_quart_in_1[i]) - $signed(exp_quart_in_0[i]);
            adder_in_0[i*QUART_L + 1 +: MANT_QUART_L] = mant_quart_in_1[i];
            adder_in_1_pre_shift[i*QUART_L + 1 +: MANT_QUART_L] = mant_quart_in_0[i];
            bigger_exp_quart[i]= $signed(exp_quart_in_1[i]);
          end
        end
      end

    endcase
  end
  
  // shift_val generation
  always_comb begin
    shift_val = '0;

    case (mode) 
      pe_pkg::PRECISION_CONFIG_32B : begin 
        foreach (shift_val[i]) begin
          if (exp_full_diff > MAX_SHIFT_FULL) begin
            shift_val[i] = MAX_SHIFT_FULL;
          end else begin
            shift_val[i] = exp_full_diff;
          end
        end
      end
      pe_pkg::PRECISION_CONFIG_16B : begin 
        foreach (shift_val[i]) begin
          if (exp_half_diff[i/2] > MAX_SHIFT_HALF) begin
            shift_val[i] = MAX_SHIFT_HALF;
          end else begin
            shift_val[i] = exp_half_diff[i/2];
          end
        end
      end
      pe_pkg::PRECISION_CONFIG_8B : begin 
        foreach (shift_val[i]) begin
          if (exp_quart_diff[i] > MAX_SHIFT_QUART) begin
            shift_val[i] = MAX_SHIFT_QUART;
          end else begin
            shift_val[i] = exp_quart_diff[i];
          end
        end
      end
    endcase
  end

  // right shift the smaller mantissa
  right_shift_decomposable #(.ARITH_SHIFT(0), .EXTENSION_BIT(0)) RIGHT_SHIFT_DECOMPOSABLE_INS(
    .in       (adder_in_1_pre_shift),
    .shift_val(shift_val),
    .full_shift (1'b0), // Need not full_shift ever because 1 will never be in MSB, as FULL_L is always bigger than MANT_FULL_L
    .mode     (mode),
    .out      (adder_in_1_post_shift)
  );
  
  adder_decomposable #(.EACH_ADDER_LEN(QUART_L), .N_ADDERS(4)) ADDER_DECOMPOSABLE_INS (
    .in0      (adder_in_0),
    .in1      (adder_in_1_post_shift),
    .mode     (mode),

    .out_quart(adder_out_quart),
    .out_half (adder_out_half ),
    .out_full (adder_out_full )
  ); 
  
  assign adder_mant_out_full = adder_out_full[0 +: (MANT_FULL_L + 2)];
  always_comb begin
    foreach ( adder_mant_out_half[i]) begin
      adder_mant_out_half[i] = adder_out_half[i][0 +: (MANT_HALF_L + 2)];
    end
  end
  always_comb begin
    foreach ( adder_mant_out_quart[i]) begin
      adder_mant_out_quart[i] = adder_out_quart[i][0 +: (MANT_QUART_L + 2)];
    end
  end

  always_comb begin
    if (mant_full_in_0 == '0) begin
      exp_full_out_pre = $signed(exp_full_in_1);
      mant_full_out_pre= {mant_full_in_1, 1'b0};
    end else if (mant_full_in_1 == '0) begin
      exp_full_out_pre = $signed(exp_full_in_0);
      mant_full_out_pre= {mant_full_in_0, 1'b0};
    end else begin
      exp_full_out_pre = bigger_exp_full;
      mant_full_out_pre  = adder_mant_out_full;
    end
  end
  always_comb begin
    foreach (exp_half_out_pre[i]) begin
      if (mant_half_in_0[i] == '0) begin
        exp_half_out_pre[i] = $signed(exp_half_in_1[i]);
        mant_half_out_pre[i]= {mant_half_in_1[i], 1'b0};
      end else if (mant_half_in_1[i] == '0) begin
        exp_half_out_pre[i] = $signed(exp_half_in_0[i]);
        mant_half_out_pre[i]= {mant_half_in_0[i], 1'b0};
      end else begin
        exp_half_out_pre[i] = bigger_exp_half[i];
        mant_half_out_pre[i]  = adder_mant_out_half[i];
      end
    end
  end
  always_comb begin
    foreach (exp_quart_out_pre[i]) begin
      if (mant_quart_in_0[i] == '0) begin
        exp_quart_out_pre[i] = $signed(exp_quart_in_1[i]);
        mant_quart_out_pre[i]= {mant_quart_in_1[i], 1'b0};
      end else if (mant_quart_in_1[i] == '0) begin
        exp_quart_out_pre[i] = $signed(exp_quart_in_0[i]);
        mant_quart_out_pre[i]= {mant_quart_in_0[i], 1'b0};
      end else begin
        exp_quart_out_pre[i] = bigger_exp_quart[i];
        mant_quart_out_pre[i]  = adder_mant_out_quart[i];
      end
    end
  end

  assign exp_full_out = exp_full_out_pre;
  assign exp_half_out = exp_half_out_pre;
  assign exp_quart_out= exp_quart_out_pre;

  assign mant_full_out  = mant_full_out_pre;
  assign mant_half_out  = mant_half_out_pre;
  assign mant_quart_out = mant_quart_out_pre;


endmodule

`endif //FLT_ADDER_DECOMPOSABLE_DEF
