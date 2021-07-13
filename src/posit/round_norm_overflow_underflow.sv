//=======================================================================
// Created by         : KU Leuven
// Filename           : round_norm_overflow_underflow.sv
// Author             : Nimish Shah
// Created On         : 2019-12-30 16:02
// Last Modified      : 
// Update Count       : 2019-12-30 16:02
// Description        : 
//                      
//=======================================================================

`ifndef ROUND_NORM_OVERFLOW_UNDERFLOW_DEF
  `define ROUND_NORM_OVERFLOW_UNDERFLOW_DEF
  
  `include "posit_pkg.sv"

module round_norm_overflow_underflow (
  input [posit_pkg::EXP_COMBINED_FULL_L : 0] exp_full_in,
  input [1:0] [posit_pkg::EXP_COMBINED_HALF_L : 0] exp_half_in,
  input [3:0] [posit_pkg::EXP_COMBINED_QUART_L : 0] exp_quart_in,

  input [posit_pkg::MANT_FULL_L + 1 : 0] mant_full_in,
  input [1 : 0] [posit_pkg::MANT_HALF_L + 1 : 0] mant_half_in,
  input [3 : 0] [posit_pkg::MANT_QUART_L + 1 : 0] mant_quart_in,

  output posit_pkg::exp_full_t         exp_full_out,
  output posit_pkg::mant_full_t       mant_full_out,

  output posit_pkg::exp_half_t   [1:0] exp_half_out,
  output posit_pkg::mant_half_t  [1:0] mant_half_out,
                                            
  output posit_pkg::exp_quart_t  [3:0] exp_quart_out,
  output posit_pkg::mant_quart_t [3:0] mant_quart_out
); 
  import posit_pkg::*;

  localparam MAX_EXP_FULL= (FULL_L - 2) << ES_FULL_L; // 2**(EXP_COMBINED_FULL_L - 1) -1;  
  localparam MIN_EXP_FULL= (-FULL_L + 1) << ES_FULL_L; //-(2**(EXP_COMBINED_FULL_L -1));  

  localparam MAX_EXP_HALF= (HALF_L - 2) << ES_HALF_L; //2**(EXP_COMBINED_HALF_L - 1) -1;  
  localparam MIN_EXP_HALF= (-HALF_L + 1) << ES_HALF_L;//-(2**(EXP_COMBINED_HALF_L -1));  

  localparam MAX_EXP_QUART= (QUART_L - 2) << ES_QUART_L;// 2**(EXP_COMBINED_QUART_L - 1) -1;  
  localparam MIN_EXP_QUART= (-QUART_L + 1) << ES_QUART_L;// -(2**(EXP_COMBINED_QUART_L -1));  

  posit_pkg::exp_full_t         exp_full_out_pre;
  posit_pkg::mant_full_t       mant_full_out_pre;
  
  posit_pkg::exp_half_t   [1:0] exp_half_out_pre;
  posit_pkg::mant_half_t  [1:0] mant_half_out_pre;

  posit_pkg::exp_quart_t  [3:0] exp_quart_out_pre;
  posit_pkg::mant_quart_t [3:0] mant_quart_out_pre;

  logic [2:0] [3:0] norm; // for all precisions, used to increament exp

  // for round irrespective of normalization
  logic [MANT_FULL_L : 0]       mant_full_post_round,  mant_full_post_norm;
  logic [1:0][MANT_HALF_L : 0]  mant_half_post_round,  mant_half_post_norm;
  logic [3:0][MANT_QUART_L : 0] mant_quart_post_round, mant_quart_post_norm;
  
  // 1 bit extra than exp
  logic [EXP_COMBINED_FULL_L : 0]        exp_full_post_norm , exp_full_post_round ;
  logic [1:0] [EXP_COMBINED_HALF_L : 0]  exp_half_post_norm , exp_half_post_round ;
  logic [3:0] [EXP_COMBINED_QUART_L : 0] exp_quart_post_norm, exp_quart_post_round ;
  
  // regime needed to find the bit that is to be rounded
  logic [REGIME_FULL_L : 0]          regime_full_post_round , regime_full_post_norm;
  logic [1 : 0] [REGIME_HALF_L : 0]  regime_half_post_round , regime_half_post_norm;
  logic [3 : 0] [REGIME_QUART_L : 0] regime_quart_post_round, regime_quart_post_norm;
  
  // pointer to rounding bit
  logic [$clog2(ES_FULL_L + MANT_FULL_L) : 0]         round_bit_ptr_full;
  logic [1: 0][$clog2(ES_HALF_L + MANT_HALF_L) : 0]   round_bit_ptr_half;
  logic [3: 0][$clog2(ES_QUART_L + MANT_QUART_L) : 0] round_bit_ptr_quart;
  
  // num does not contain the explicit 1 in mantissa, but has an extra round bit at the end
  logic [EXP_COMBINED_FULL_L + 1 + MANT_FULL_L - 1: 0 ]           num_pre_round_full ;
  logic [1 : 0] [EXP_COMBINED_HALF_L + 1 + MANT_HALF_L - 1: 0 ]   num_pre_round_half ;
  logic [3 : 0] [EXP_COMBINED_QUART_L + 1 + MANT_QUART_L - 1: 0 ] num_pre_round_quart;
  
  // 1 extra bit for combined exp, no explicit bit in mantissa
  logic [EXP_COMBINED_FULL_L + MANT_FULL_L - 1: 0 ]           num_post_round_full;
  logic [1 : 0] [EXP_COMBINED_HALF_L + MANT_HALF_L - 1: 0 ]   num_post_round_half;
  logic [3 : 0] [EXP_COMBINED_QUART_L + MANT_QUART_L - 1: 0 ] num_post_round_quart;

  // rounding val to add
  // One extra bit is towards the MSB, beyond ES field
  // Using 2 extra fields to avoid confusing with -ve numbers when MSB becomes 1
  logic [ES_FULL_L + MANT_FULL_L + 1: 0]         round_val_full;
  logic [1: 0][ES_HALF_L + MANT_HALF_L + 1: 0]   round_val_half;
  logic [3: 0][ES_QUART_L + MANT_QUART_L + 1: 0] round_val_quart;

  // check if normalization has to be done
  assign norm[0][0]= mant_full_in[MANT_FULL_L + 1];
  always_comb begin
    foreach ( mant_half_in[i]) begin
      norm[1][i] = mant_half_in[i][MANT_HALF_L + 1];
    end
  end
  always_comb begin
    foreach ( mant_quart_in[i]) begin
      norm[2][i] = mant_quart_in[i][MANT_QUART_L + 1];
    end
  end
  
  // Normalize 
  // The extra bit in mantissa MIGHT be needed for rounding
  always_comb begin
    if (norm[0][0]) begin
      exp_full_post_norm = $signed(exp_full_in) + 1;
      mant_full_post_norm = mant_full_in[1 +: (MANT_FULL_L + 1)];
    end else begin
      exp_full_post_norm = exp_full_in;
      mant_full_post_norm = mant_full_in[0 +: (MANT_FULL_L + 1)];
    end
  end
  always_comb begin
    foreach ( exp_half_post_norm[i]) begin
      if (norm[1][i]) begin
        exp_half_post_norm[i] = $signed(exp_half_in[i]) + 1;
        mant_half_post_norm[i] = mant_half_in[i][1 +: MANT_HALF_L + 1];
      end else begin
        exp_half_post_norm[i] = exp_half_in[i];
        mant_half_post_norm[i] = mant_half_in[i][0 +: MANT_HALF_L + 1];
      end
    end
  end
  always_comb begin
    foreach ( exp_quart_post_norm[i]) begin
      if (norm[2][i]) begin
        exp_quart_post_norm[i] = $signed(exp_quart_in[i]) + 1;
        mant_quart_post_norm[i] = mant_quart_in[i][1 +: MANT_QUART_L + 1];
      end else begin
        exp_quart_post_norm[i] = exp_quart_in[i];
        mant_quart_post_norm[i] = mant_quart_in[i][0 +: MANT_QUART_L + 1];
      end
    end
  end
  
  // Round
  assign regime_full_post_norm = exp_full_post_norm[ ES_FULL_L +: $bits(regime_full_post_norm)];
  always_comb begin
    foreach (regime_half_post_norm[i]) begin
      regime_half_post_norm[i] = exp_half_post_norm[i][ ES_HALF_L +: $bits(regime_half_post_norm[i])];
    end
  end
  always_comb begin
    foreach (regime_quart_post_norm[i]) begin
      regime_quart_post_norm[i] = exp_quart_post_norm[i][ ES_QUART_L +: $bits(regime_quart_post_norm[i])];
    end
  end

  // couple exp and mant, while removing the explicit 1 in mantissa
  assign num_pre_round_full = {exp_full_post_norm, mant_full_post_norm[0 +: MANT_FULL_L]};
  always_comb begin
    foreach (num_pre_round_half[i]) begin
      num_pre_round_half[i] = {exp_half_post_norm[i], mant_half_post_norm[i][0 +: MANT_HALF_L]};
    end
  end
  always_comb begin
    foreach (num_pre_round_quart[i]) begin
      num_pre_round_quart[i] = {exp_quart_post_norm[i], mant_quart_post_norm[i][0 +: MANT_QUART_L]};
    end
  end
  
  // generate the round value to add, depending on regime
  always_comb begin
    round_val_full = 'x;
    round_bit_ptr_full = 'x;
    if ( ($signed(exp_full_post_norm) >= MAX_EXP_FULL) || ($signed(exp_full_post_norm) <= MIN_EXP_FULL)) begin
      round_val_full = '0;
      round_bit_ptr_full= 'x;
    end else begin
      if ($signed(regime_full_post_norm) < 0) begin
        round_bit_ptr_full = 0 - $signed(regime_full_post_norm) - 1;
      end else begin
        round_bit_ptr_full = $signed(regime_full_post_norm);
      end
      round_val_full = (num_pre_round_full[round_bit_ptr_full] << round_bit_ptr_full);
    end
  end
  always_comb begin
    round_val_half = 'x;
    round_bit_ptr_half = 'x;

    foreach ( round_val_half[i]) begin
      if ( ($signed(exp_half_post_norm[i]) >= MAX_EXP_HALF) || ($signed(exp_half_post_norm[i]) <= MIN_EXP_HALF)) begin
        round_val_half[i] = '0;
        round_bit_ptr_half[i]= 'x;
      end else begin
        if ($signed(regime_half_post_norm[i]) < 0) begin
          round_bit_ptr_half[i] = 0 - $signed(regime_half_post_norm[i]) - 1;
        end else begin
          round_bit_ptr_half[i] = $signed(regime_half_post_norm[i]);
        end
        round_val_half[i] = (num_pre_round_half[i][round_bit_ptr_half[i]] << round_bit_ptr_half[i]);
      end
    end
  end
  always_comb begin
    round_val_quart = 'x;
    round_bit_ptr_quart = 'x;

    foreach ( round_val_quart[i]) begin
      if ( ($signed(exp_quart_post_norm[i]) >= MAX_EXP_QUART) || ($signed(exp_quart_post_norm[i]) <= MIN_EXP_QUART)) begin
        round_val_quart[i] = '0;
        round_bit_ptr_quart[i]= 'x;
      end else begin
        if ($signed(regime_quart_post_norm[i]) < 0) begin
          round_bit_ptr_quart[i] = 0 - $signed(regime_quart_post_norm[i]) - 1;
        end else begin
          round_bit_ptr_quart[i] = $signed(regime_quart_post_norm[i]);
        end
        round_val_quart[i] = (num_pre_round_quart[i][round_bit_ptr_quart[i]] << round_bit_ptr_quart[i]);
      end
    end
  end

  assign num_post_round_full = num_pre_round_full[1 +: EXP_COMBINED_FULL_L + MANT_FULL_L] + $unsigned(round_val_full);
  always_comb begin
    foreach ( num_pre_round_half[i]) begin
      num_post_round_half[i] = num_pre_round_half[i][1 +: EXP_COMBINED_HALF_L + MANT_HALF_L] + $unsigned(round_val_half[i]);
    end
  end
  always_comb begin
    foreach ( num_pre_round_quart[i]) begin
      num_post_round_quart[i] = num_pre_round_quart[i][1 +: EXP_COMBINED_QUART_L + MANT_QUART_L] + $unsigned(round_val_quart[i]);
    end
  end

  assign regime_full_post_round = num_post_round_full[ ES_FULL_L + MANT_FULL_L - 1+: $bits(regime_full_post_round)];
  always_comb begin
    foreach (regime_half_post_round[i]) begin
      regime_half_post_round[i] = num_post_round_half[i][ ES_HALF_L + MANT_HALF_L - 1 +: $bits(regime_half_post_round[i])];
    end
  end
  always_comb begin
    foreach (regime_quart_post_round[i]) begin
      regime_quart_post_round[i] = num_post_round_quart[i][ ES_QUART_L + MANT_QUART_L - 1 +: $bits(regime_quart_post_round[i])];
    end
  end

  assign exp_full_post_round = ($signed(regime_full_post_round) == $signed(regime_full_post_norm) + 1) ? {regime_full_post_round, {ES_FULL_L{1'b0}}} : num_post_round_full[MANT_FULL_L - 1 +: EXP_COMBINED_FULL_L + 1];
  always_comb begin
    foreach (exp_half_post_round[i]) begin
      if ($signed(regime_half_post_round[i]) == $signed(regime_half_post_norm[i]) + 1) begin
        exp_half_post_round[i] = {regime_half_post_round[i], {ES_HALF_L{1'b0}}};
      end else begin
        exp_half_post_round[i] = num_post_round_half[i][MANT_HALF_L - 1 +: EXP_COMBINED_HALF_L + 1];
      end
    end
  end
  always_comb begin
    foreach (exp_quart_post_round[i]) begin
      if ($signed(regime_quart_post_round[i]) == $signed(regime_quart_post_norm[i]) + 1) begin
        exp_quart_post_round[i] = {regime_quart_post_round[i], {ES_QUART_L{1'b0}}};
      end else begin
        exp_quart_post_round[i] = num_post_round_quart[i][MANT_QUART_L - 1 +: EXP_COMBINED_QUART_L + 1];
      end
    end
  end

  always_comb begin
    if (($signed(exp_full_post_round) == $signed(exp_full_post_norm) + 1) || 
        ($signed(regime_full_post_round) == $signed(regime_full_post_norm) + 1)) begin
      mant_full_post_round = {mant_full_post_norm[MANT_FULL_L ], {(MANT_FULL_L -1){1'b0}}}; //, num_post_round_full[MANT_FULL_L -2 -: MANT_FULL_L -2 ]};
    end else begin
      mant_full_post_round = {mant_full_post_norm[MANT_FULL_L ], num_post_round_full[MANT_FULL_L -2 -: MANT_FULL_L -1 ]};
    end
  end
  always_comb begin
    foreach (mant_half_post_round[i]) begin
      if (($signed(exp_half_post_round[i]) == $signed(exp_half_post_norm[i]) + 1) || 
          ($signed(regime_half_post_round[i]) == $signed(regime_half_post_norm[i]) + 1)) begin
        mant_half_post_round[i] = {mant_half_post_norm[i][MANT_HALF_L ], {(MANT_HALF_L -1){1'b0}}}; 
        //mant_half_post_round[i] = {mant_half_post_norm[i][MANT_HALF_L ], 1'b0, num_post_round_half[i][MANT_HALF_L -2 -: MANT_HALF_L -2 ]};
      end else begin
        mant_half_post_round[i] = {mant_half_post_norm[i][MANT_HALF_L ], num_post_round_half[i][MANT_HALF_L -2 -: MANT_HALF_L -1 ]};
      end
    end
  end
  always_comb begin
    foreach (mant_quart_post_round[i]) begin
      if (($signed(exp_quart_post_round[i]) == $signed(exp_quart_post_norm[i]) + 1) || 
          ($signed(regime_quart_post_round[i]) == $signed(regime_quart_post_norm[i]) + 1)) begin
        mant_quart_post_round[i] = {mant_quart_post_norm[i][MANT_QUART_L ], {(MANT_QUART_L -1){1'b0}}}; 
      //  mant_quart_post_round[i] = {mant_quart_post_norm[i][MANT_QUART_L ], 1'b0, num_post_round_quart[i][MANT_QUART_L -2 -: MANT_QUART_L -2 ]};
      end else begin
        mant_quart_post_round[i] = {mant_quart_post_norm[i][MANT_QUART_L ], num_post_round_quart[i][MANT_QUART_L -2 -: MANT_QUART_L -1 ]};
      end
    end
  end

  // Overflow - underflow check
  always_comb begin
    mant_full_out_pre = 'x;
    if ($signed(exp_full_post_round) > MAX_EXP_FULL) begin 
      exp_full_out_pre = MAX_EXP_FULL;
    end else if ($signed(exp_full_post_round) < MIN_EXP_FULL) begin
      exp_full_out_pre = MIN_EXP_FULL;
    end else begin
      exp_full_out_pre = exp_full_post_round;
      mant_full_out_pre = mant_full_post_round;
    end
  end

  always_comb begin
    foreach ( exp_half_out_pre[i]) begin
      mant_half_out_pre[i] = 'x;
      if ($signed(exp_half_post_round[i]) > MAX_EXP_HALF) begin 
        exp_half_out_pre[i] = MAX_EXP_HALF;
      end else if ($signed(exp_half_post_round[i]) < MIN_EXP_HALF) begin
        exp_half_out_pre[i] = MIN_EXP_HALF;
      end else begin
        exp_half_out_pre[i] = exp_half_post_round[i];
        mant_half_out_pre[i] = mant_half_post_round[i];
      end
    end
  end
  always_comb begin
    foreach ( exp_quart_out_pre[i]) begin
        mant_quart_out_pre[i] = 'x;
      if ($signed(exp_quart_post_round[i]) > MAX_EXP_QUART) begin 
        exp_quart_out_pre[i] = MAX_EXP_QUART;
      end else if ($signed(exp_quart_post_round[i]) < MIN_EXP_QUART) begin
        exp_quart_out_pre[i] = MIN_EXP_QUART;
      end else begin
        exp_quart_out_pre[i] = exp_quart_post_round[i];
        mant_quart_out_pre[i] = mant_quart_post_round[i];
      end
    end
  end

  assign exp_full_out  = exp_full_out_pre  ;
  assign mant_full_out = mant_full_out_pre ;

  assign exp_half_out  = exp_half_out_pre  ;
  assign mant_half_out = mant_half_out_pre ;

  assign exp_quart_out = exp_quart_out_pre ;
  assign mant_quart_out= mant_quart_out_pre;


endmodule


`endif //ROUND_NORM_OVERFLOW_UNDERFLOW_DEF
