//=======================================================================
// Created by         : KU Leuven
// Filename           : extract_fields.sv
// Author             : Nimish Shah
// Created On         : 2019-12-22 18:28
// Last Modified      : 
// Update Count       : 2019-12-22 18:28
// Description        : 
//                      
//=======================================================================

`ifndef EXTRACT_FIELDS_DEF
  `define EXTRACT_FIELDS_DEF
  
  `include "posit_pkg.sv"

  `include "lzd_decomposable.sv"
  `include "shifter_decomposable.sv"

module extract_fields #(ES_L_32= 6, ES_L_16= 4, ES_L_8=2) (
  input clk, // for assertion

  input [31: 0] in,
  output [ES_L_32 + $clog2(32) : 0] exp32,
  output [32 - 2 - ES_L_32 : 0] mant32,

  output [1:0][ES_L_16 + $clog2(16) : 0] exp16,
  output [1:0][16 - 2 - ES_L_16  : 0] mant16,

  output [3:0][ES_L_8 + $clog2(8) : 0] exp8,
  output [3:0][8 - 2 - ES_L_8 : 0] mant8,

  input [PRECISION_CONFIG_L - 1 : 0] mode 
);
// format:
// regime | exp | mant
// No sign bit

  localparam FULL_L= 32;
  localparam HALF_L= FULL_L/2;
  localparam QUART_L= FULL_L/4;
  
  localparam MANT_FULL_L= FULL_L -2 -ES_L_32 + 1;
  localparam MANT_HALF_L= HALF_L -2 -ES_L_16 + 1;
  localparam MANT_QUART_L= QUART_L -2 -ES_L_8 + 1;

  //===========================================
  //       Signals
  //===========================================
  logic       first_bit_32B, all_zeroes_full,  all_ones_full;
  logic [1:0] first_bit_16B, all_zeroes_half,  all_ones_half;
  logic [3:0] first_bit_8B,  all_zeroes_quart, all_ones_quart;
  
  logic signed [$clog2(FULL_L) : 0]       regime_full;
  logic signed [1:0][$clog2(HALF_L) : 0]  regime_half;
  logic signed [3:0][$clog2(QUART_L) : 0] regime_quart;
  
  logic unsigned [ES_L_32 - 1 : 0]        exp_fx_len_full;
  logic unsigned [1 : 0][ES_L_16 - 1 : 0] exp_fx_len_half;
  logic unsigned [3 : 0][ES_L_8 - 1 : 0]  exp_fx_len_quart;

  logic [$bits(regime_full) + $bits(exp_fx_len_full) - 1 : 0]               exp_full;
  logic [1:0] [$bits(regime_half[0]) + $bits(exp_fx_len_half[0]) - 1 : 0]   exp_half;
  logic [3:0] [$bits(regime_quart[0]) + $bits(exp_fx_len_quart[0]) - 1 : 0] exp_quart;
  
  logic [MANT_FULL_L - 1: 0]      mant_full;
  logic [1:0][MANT_HALF_L - 1: 0] mant_half;
  logic [3:0][MANT_QUART_L - 1: 0] mant_quart;

  // lzd related
  logic [FULL_L - 1 : 0] lzd_in;
  logic [$clog2(FULL_L) - 1 : 0]         lzd_out_full;
  logic                                  lzd_all_ones_full;

  logic [1 : 0][$clog2(HALF_L) - 1 : 0]  lzd_out_half;
  logic [1 : 0]                          lzd_all_ones_half;

  logic [3 : 0][$clog2(QUART_L) - 1 : 0] lzd_out_quart;
  logic [3 : 0]                          lzd_all_ones_quart;
  
  // shifter related
  logic [3:0][$clog2(FULL_L) - 1 : 0] shift_val;
  logic full_shift;
  logic [FULL_L - 1 : 0] shift_out;

  // Basic info extraction
  assign first_bit_32B = in[FULL_L - 1];
  assign first_bit_16B[0] = in[HALF_L - 1];
  assign first_bit_16B[1] = in[2 * HALF_L - 1];
  assign first_bit_8B[0] = in[QUART_L - 1];
  assign first_bit_8B[1] = in[2 * QUART_L - 1];
  assign first_bit_8B[2] = in[3 * QUART_L - 1];
  assign first_bit_8B[3] = in[4 * QUART_L - 1];

  assign all_zeroes_full = (in == '0) ? 1 : 0;
  assign all_ones_full = (in == '1) ? 1 : 0;
  always_comb begin
    for (integer i=0; i< 2; i=i+1) begin
      all_zeroes_half[i] = (in[i*HALF_L +: HALF_L] == '0) ? 1 : 0;
      all_ones_half[i] = (in[i*HALF_L +: HALF_L] == '1) ? 1 : 0;
    end
  end
  always_comb begin
    for (integer i=0; i< 4; i=i+1) begin
      all_zeroes_quart[i] = (in[i*QUART_L +: QUART_L] == '0) ? 1 : 0;
      all_ones_quart[i] = (in[i*QUART_L +: QUART_L] == '1) ? 1 : 0;
    end
  end

  // Extract input to LZD to find the length of regime
  always_comb begin
    case (mode) 
      pe_pkg::PRECISION_CONFIG_32B : begin 
        lzd_in = first_bit_32B ? in : ~in;
      end

      pe_pkg::PRECISION_CONFIG_16B : begin 
        for (integer i=0; i< 2; i=i+1) begin
          lzd_in[i*HALF_L +: HALF_L] = first_bit_16B[i] ? in[i*HALF_L +: HALF_L] : ~in[i*HALF_L +: HALF_L]; 
        end
      end

      pe_pkg::PRECISION_CONFIG_8B : begin 
        for (integer i=0; i< 4; i=i+1) begin
          lzd_in[i*QUART_L +: QUART_L] = first_bit_8B[i] ? in[i*QUART_L +: QUART_L] : ~in[i*QUART_L +: QUART_L]; 
        end
      end
      
      default : lzd_in= 'x;
    endcase
  end

  // LZD to detect location of exp and mant
  lzd_decomposable #(.MAX_BITS(FULL_L)) LZD_DECOMPOSABLE_INS (
    .in              (lzd_in),
    .out_full        (lzd_out_full        ),
    .all_ones_full   (lzd_all_ones_full   ),
  
    .out_half        (lzd_out_half        ),
    .all_ones_half   (lzd_all_ones_half   ),
 
    .out_quarter     (lzd_out_quart),
    .all_ones_quarter(lzd_all_ones_quart)
  ); 
  
  always_comb begin
    regime_full = 'x;
    regime_half = 'x;
    regime_quart= 'x;
    shift_val= 'x;
    full_shift= 1'b0;

    case (mode) 
      pe_pkg::PRECISION_CONFIG_32B : begin 
        if (all_zeroes_full) begin
          regime_full = '0;
          shift_val = '0;
        end else begin
          if (first_bit_32B == 1) begin
            regime_full = FULL_L - 1 - lzd_out_full - 1;
          end else begin
            regime_full = - FULL_L + 1 + lzd_out_full;
          end
          for (integer i=0; i< 4; i=i+1) begin
            shift_val[i] = FULL_L - lzd_out_full;
          end
          if (lzd_out_full == 0) begin
            full_shift = 1'b1;
          end
        end
      end
     
      pe_pkg::PRECISION_CONFIG_16B : begin 
        for (integer i=0; i< 2; i=i+1) begin
          if (all_zeroes_half[i]) begin
            regime_half[i] = '0;
            shift_val[i*2] = '0;
            shift_val[i*2 + 1] = '0;
          end else begin
            if (first_bit_16B[i] == 1) begin
              regime_half[i] = HALF_L - 1 - lzd_out_half[i] - 1;
            end else begin
              regime_half[i] = -HALF_L + 1 + lzd_out_half[i];
            end
            shift_val[i*2] = HALF_L - lzd_out_half[i];
            shift_val[i*2 + 1] = HALF_L - lzd_out_half[i];
          end
        end
      end
      
      pe_pkg::PRECISION_CONFIG_8B : begin 
        for (integer i=0; i< 4; i=i+1) begin
          if (all_zeroes_quart[i]) begin
            regime_quart[i] = '0;
            shift_val[i] = '0;
          end else begin
            if (first_bit_8B[i] == 1) begin
              regime_quart[i] = QUART_L - 1 - lzd_out_quart[i] - 1;
            end else begin
              regime_quart[i] = -QUART_L + 1 + lzd_out_quart[i];
            end
            shift_val[i] = QUART_L - lzd_out_quart[i];
          end
        end
      end
    
    endcase
  end

  // shifter
  left_shift_decomposable #(.ARITH_SHIFT(0), .EXTENSION_BIT(0)) LEFT_SHIFT_DECOMPOSABLE_INS(
    .in       (in),
    .shift_val(shift_val),
    .full_shift (full_shift),
    .mode     (mode),
    .out      (shift_out)
  );
  
  // extract exponent
  assign exp_full = {regime_full, shift_out[FULL_L - 1 -: ES_L_32]};
  always_comb begin
    foreach (exp_half[i]) begin
      exp_half[i] = {regime_half[i], shift_out[(i+1)*HALF_L -1 -: ES_L_16]};
    end
  end
  always_comb begin
    foreach ( exp_quart[i]) begin
      exp_quart[i]= {regime_quart[i], shift_out[(i+1)*QUART_L -1 -: ES_L_8]};
    end
  end

  // extract mantissa
  assign mant_full = {~all_zeroes_full, shift_out[FULL_L - 1 - ES_L_32 -: MANT_FULL_L - 1]};
  always_comb begin
    foreach ( mant_half[i]) begin
      mant_half[i] = {~all_zeroes_half[i], shift_out[(i+1)*HALF_L - 1 - ES_L_16 -: MANT_HALF_L - 1]};
    end
  end
  always_comb begin
    foreach ( mant_quart[i]) begin
      mant_quart[i] = {~all_zeroes_quart[i], shift_out[(i+1)*QUART_L - 1 - ES_L_8  -: MANT_QUART_L - 1]};
    end
  end

  assign exp32 = exp_full;
  assign mant32 = mant_full;

  assign exp16 = exp_half;
  assign mant16 = mant_half;

  assign exp8 = exp_quart;
  assign mant8 = mant_quart;

  //===========================================
  //      Assertions 
  //===========================================
  assert property (@(posedge clk) ~all_ones_full) else $warning(1);
  assert property (@(posedge clk) if (mode == pe_pkg::PRECISION_CONFIG_16B) (all_ones_half == '0)) else $warning(1);
  assert property (@(posedge clk) if (mode == pe_pkg::PRECISION_CONFIG_8B) (all_ones_quart == '0)) else $warning(1);

endmodule


`endif //EXTRACT_FIELDS_DEF
