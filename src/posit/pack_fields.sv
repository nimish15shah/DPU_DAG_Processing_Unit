//=======================================================================
// Created by         : KU Leuven
// Filename           : pack_filed.sv
// Author             : Nimish Shah
// Created On         : 2019-12-24 14:41
// Last Modified      : 
// Update Count       : 2019-12-24 14:41
// Description        : 
//                      
//=======================================================================

`ifndef PACK_FIELDS_DEF
  `define PACK_FIELDS_DEF

  `include "posit_pkg.sv"
  `include "shifter_decomposable.sv"

module pack_fields (
  output [posit_pkg::FULL_L -1 : 0] out,

  input  posit_pkg::exp_full_t         exp_full,
  input  posit_pkg::mant_full_t       mant_full,

  input  posit_pkg::exp_half_t   [1:0] exp_half,
  input  posit_pkg::mant_half_t  [1:0] mant_half,
                                       
  input  posit_pkg::exp_quart_t  [3:0] exp_quart,
  input  posit_pkg::mant_quart_t [3:0] mant_quart,

  input [PRECISION_CONFIG_L - 1 : 0] mode 
); 

  import posit_pkg::*;
  
  logic [FULL_L - 1 : 0] out_pre;
  
  logic all_zeroes_full;
  logic [1:0] all_zeroes_half;
  logic [3:0] all_zeroes_quart;

  logic [FULL_L - 1 : 0] shift_in_reversed;
  logic [FULL_L - 1 : 0] shift_out_reversed;
  logic [FULL_L - 1 : 0] shift_in;
  logic [FULL_L - 1 : 0] shift_out;
  
  exp_fx_len_full_t        exp_fx_len_full;
  exp_fx_len_half_t [1:0]  exp_fx_len_half;
  exp_fx_len_quart_t [3:0] exp_fx_len_quart;
  
  regime_full_t        regime_full;
  regime_half_t [1:0]  regime_half;
  regime_quart_t [3:0] regime_quart;

  logic [3:0] [$bits(regime_full) - 2:0] shift_val;
  
  assign all_zeroes_full = (mant_full == 0) ? 1 : 0;
  always_comb begin
    foreach (all_zeroes_half[i]) begin
      all_zeroes_half[i] = (mant_half[i] == 0) ? 1 : 0;
    end
  end
  always_comb begin
    foreach (all_zeroes_quart[i]) begin
      all_zeroes_quart[i] = (mant_quart[i] == 0) ? 1 : 0;
    end
  end


  assign regime_full = exp_full >> ES_FULL_L;
  assign exp_fx_len_full = exp_full[0 +: ES_FULL_L];
  always_comb begin
    foreach ( regime_half[i]) begin
      regime_half[i] = exp_half[i] >> ES_HALF_L;
      exp_fx_len_half[i] = exp_half[i][0 +: ES_HALF_L];
    end
  end
  always_comb begin
    foreach ( regime_quart[i]) begin
      regime_quart[i] = exp_quart[i] >> ES_QUART_L;
      exp_fx_len_quart[i] = exp_quart[i][0 +: ES_QUART_L];
    end
  end

  // based on the MSB of regime (sign of regime), pad with 01 or 10
  // remove the MSB- implicit bit of manitssa
  always_comb begin
    shift_in= 'x;
    case (mode) 
      pe_pkg::PRECISION_CONFIG_32B : begin 
        if (regime_full[$bits(regime_full) - 1] == 0) begin
          shift_in = {2'b10, exp_fx_len_full, mant_full[0 +: MANT_FULL_L - 1]};
        end else begin
          shift_in = {2'b01, exp_fx_len_full, mant_full[0 +: MANT_FULL_L - 1]};
        end

        if (all_zeroes_full) begin
          shift_in = '0;
        end
      end

      pe_pkg::PRECISION_CONFIG_16B : begin 
        foreach (regime_half[i]) begin
          if (regime_half[i][$bits(regime_half[i]) - 1] == 0) begin
            shift_in[i*HALF_L +: HALF_L] = {2'b10, exp_fx_len_half[i], mant_half[i][0 +: MANT_HALF_L - 1]};
          end else begin
            shift_in[i*HALF_L +: HALF_L] = {2'b01, exp_fx_len_half[i], mant_half[i][0 +: MANT_HALF_L - 1]};
          end
          if (all_zeroes_half[i]) begin
            shift_in[i*HALF_L +: HALF_L] = '0;
          end
        end
      end

      pe_pkg::PRECISION_CONFIG_8B : begin 
        foreach (regime_quart[i]) begin
          if (regime_quart[i][$bits(regime_quart[i]) - 1] == 0) begin
            shift_in[i*QUART_L +: QUART_L] = {2'b10, exp_fx_len_quart[i], mant_quart[i][0 +: MANT_QUART_L - 1]};
          end else begin
            shift_in[i*QUART_L +: QUART_L] = {2'b01, exp_fx_len_quart[i], mant_quart[i][0 +: MANT_QUART_L - 1]};
          end
          if (all_zeroes_quart[i]) begin
            shift_in[i*QUART_L +: QUART_L] = '0;
          end
        end
      end
    endcase
  end

  always_comb begin
    shift_val = 'x;
    case (mode) 
      pe_pkg::PRECISION_CONFIG_32B : begin 
        foreach (shift_val[i]) begin

          if (regime_full[$bits(regime_full) - 1]) begin
            shift_val[i] = (0 - $signed(regime_full) - 1);
          end else begin
            shift_val[i] = regime_full;
          end
//          shift_val[i] =  ? (-regime_full - 1) : regime_full;
        end
      end
      pe_pkg::PRECISION_CONFIG_16B : begin 
        foreach (shift_val[i]) begin
          if (regime_half[i/2][$bits(regime_half[i/2]) - 1]) begin
            shift_val[i] = 0 - $signed(regime_half[i/2]) - 1;
          end else begin
            shift_val[i] = regime_half[i/2];
          end
//          shift_val[i] = regime_half[i/2][$bits(regime_half[i/2]) - 1] ? (-regime_half[i/2] - 1) : regime_half[i/2];
        end
      end
      pe_pkg::PRECISION_CONFIG_8B : begin 
        foreach (shift_val[i]) begin
          if (regime_quart[i][$bits(regime_quart[i]) - 1]) begin
            shift_val[i] = 0 - $signed(regime_quart[i]) - 1;
          end else begin
            shift_val[i] = regime_quart[i];
          end
//          shift_val[i] = regime_quart[i][$bits(regime_quart[i]) - 1] ?  $signed(regime_quart[i]) : regime_quart[i];
        end
      end
    endcase
  end
  
  right_shift_decomposable #(.ARITH_SHIFT(1)) RIGHT_SHIFT_DECOMPOSABLE_INS(
    .in       (shift_in),
    .shift_val(shift_val),
    .full_shift (1'b0), 
    .mode     (mode),
    .out      (shift_out)
  );

  assign out = shift_out;

endmodule

`endif //PACK_FIELDS_DEF
