`ifndef POSIT_PKG_DEF
  `define POSIT_PKG_DEF

`include "../common.sv"

package posit_pkg;
  
  parameter FULL_L= 32;
  parameter HALF_L= FULL_L/2;
  parameter QUART_L= FULL_L/4;
  
  parameter ES_FULL_L = 6;
  parameter ES_HALF_L = 4;
  parameter ES_QUART_L = 2;

  parameter REGIME_FULL_L = $clog2(FULL_L) + 1;
  parameter REGIME_HALF_L = $clog2(HALF_L) + 1;
  parameter REGIME_QUART_L = $clog2(QUART_L) + 1;

  parameter EXP_COMBINED_FULL_L = ES_FULL_L + $clog2(FULL_L) + 1;
  parameter EXP_COMBINED_HALF_L = ES_HALF_L + $clog2(HALF_L) + 1;
  parameter EXP_COMBINED_QUART_L = ES_QUART_L + $clog2(QUART_L) + 1;

  parameter MANT_FULL_L= FULL_L -2 -ES_FULL_L + 1;
  parameter MANT_HALF_L= HALF_L -2 -ES_HALF_L + 1;
  parameter MANT_QUART_L= QUART_L -2 -ES_QUART_L + 1;

  typedef logic [REGIME_FULL_L - 1 : 0] regime_full_t;
  typedef logic [REGIME_HALF_L - 1 : 0] regime_half_t;
  typedef logic [REGIME_QUART_L- 1 : 0] regime_quart_t;

  typedef logic [ES_FULL_L - 1 : 0] exp_fx_len_full_t;
  typedef logic [ES_HALF_L - 1 : 0] exp_fx_len_half_t;
  typedef logic [ES_QUART_L - 1 : 0] exp_fx_len_quart_t;

  typedef logic [EXP_COMBINED_FULL_L - 1: 0] exp_full_t;
  typedef logic [EXP_COMBINED_HALF_L - 1: 0] exp_half_t;
  typedef logic [EXP_COMBINED_QUART_L - 1: 0] exp_quart_t;

  typedef logic [MANT_FULL_L - 1 : 0] mant_full_t;
  typedef logic [MANT_HALF_L - 1 : 0] mant_half_t;
  typedef logic [MANT_QUART_L - 1 : 0] mant_quart_t;

endpackage: posit_pkg

`endif //POSIT_PKG_DEF
