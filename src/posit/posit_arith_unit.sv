//=======================================================================
// Created by         : KU Leuven
// Filename           : posit_arith_unit.sv
// Author             : Nimish Shah
// Created On         : 2019-12-30 17:06
// Last Modified      : 
// Update Count       : 2019-12-30 17:06
// Description        : 
//                      
//=======================================================================

`ifndef POSIT_ARITH_UNIT_DEF
  `define POSIT_ARITH_UNIT_DEF
  
  `include "posit_pkg.sv"
  `include "extract_fields.sv"
  `include "flt_adder_decomposable.sv"
  `include "flt_multiplier_decomposable.sv"
  `include "round_norm_overflow_underflow.sv"
  `include "pack_fields.sv"

module posit_arith_unit (
  input clk, // for assertion

  input [posit_pkg::FULL_L - 1 : 0] in_0,
  input [posit_pkg::FULL_L - 1 : 0] in_1,
  output[posit_pkg::FULL_L - 1 : 0] out,

  input [PRECISION_CONFIG_L - 1 : 0] mode,
  input mul_en // if 0 then add is enabled
); 

                                                   
//          in 0                       in 1          
//             |                          |          
//             |                          |          
//             |                          |          
//  +----------v---------+     +----------v---------+
//  |                    |     |                    |
//  |   extract fields   |     |   extract fields   |
//  |                    |     |                    |
//  +--------------------+     +--------------------+
//       |          |               |          |     
//       |          |               |          |     
//       v          v               v          v     
//    full exp    mant           full exp    mant    
//                                                   
//                                                   
// +-------------------+      +-------------------+  
// |                   |      |                   |  
// |   decomposable    |      |   decomposable    |  
// |   flt adder       |      |   flt mul         |  
// |                   |      |                   |  
// +-------------------+      +-------------------+  
//           -\                        /-            
//             -\                  /---              
//               --\            /--                  
//                  -\      /---                     
//              +------------------+                 
//              |                  |                 
//              |    round + norm  |                 
//              |    + overflow    |                 
//              |    + underflow   |                 
//              |    checks        |                 
//              +------------------+                 
//                        |                          
//                        |                          
//                +---------------+                  
//                |               |                  
//                |    pack       |                  
//                |    fields     |                  
//                |               |                  
//                +---------------+                  
//                        |                          
//                        |                          
//                        v                          
//                     output                        

  import posit_pkg::*;

  posit_pkg::exp_full_t         exp_full_in_0;
  posit_pkg::mant_full_t        mant_full_in_0;

  posit_pkg::exp_half_t   [1:0] exp_half_in_0;
  posit_pkg::mant_half_t  [1:0] mant_half_in_0;

  posit_pkg::exp_quart_t  [3:0] exp_quart_in_0;
  posit_pkg::mant_quart_t [3:0] mant_quart_in_0;

  posit_pkg::exp_full_t         exp_full_in_1;
  posit_pkg::mant_full_t        mant_full_in_1;

  posit_pkg::exp_half_t   [1:0] exp_half_in_1;
  posit_pkg::mant_half_t  [1:0] mant_half_in_1;

  posit_pkg::exp_quart_t  [3:0] exp_quart_in_1;
  posit_pkg::mant_quart_t [3:0] mant_quart_in_1;
  
  // adder inputs
  posit_pkg::exp_full_t         add_exp_full_in_0;
  posit_pkg::mant_full_t        add_mant_full_in_0;

  posit_pkg::exp_half_t   [1:0] add_exp_half_in_0;
  posit_pkg::mant_half_t  [1:0] add_mant_half_in_0;

  posit_pkg::exp_quart_t  [3:0] add_exp_quart_in_0;
  posit_pkg::mant_quart_t [3:0] add_mant_quart_in_0;

  posit_pkg::exp_full_t         add_exp_full_in_1;
  posit_pkg::mant_full_t        add_mant_full_in_1;

  posit_pkg::exp_half_t   [1:0] add_exp_half_in_1;
  posit_pkg::mant_half_t  [1:0] add_mant_half_in_1;

  posit_pkg::exp_quart_t  [3:0] add_exp_quart_in_1;
  posit_pkg::mant_quart_t [3:0] add_mant_quart_in_1;

  // multiplier inputs
  posit_pkg::exp_full_t         mul_exp_full_in_0;
  posit_pkg::mant_full_t        mul_mant_full_in_0;

  posit_pkg::exp_half_t   [1:0] mul_exp_half_in_0;
  posit_pkg::mant_half_t  [1:0] mul_mant_half_in_0;

  posit_pkg::exp_quart_t  [3:0] mul_exp_quart_in_0;
  posit_pkg::mant_quart_t [3:0] mul_mant_quart_in_0;

  posit_pkg::exp_full_t         mul_exp_full_in_1;
  posit_pkg::mant_full_t        mul_mant_full_in_1;

  posit_pkg::exp_half_t   [1:0] mul_exp_half_in_1;
  posit_pkg::mant_half_t  [1:0] mul_mant_half_in_1;

  posit_pkg::exp_quart_t  [3:0] mul_exp_quart_in_1;
  posit_pkg::mant_quart_t [3:0] mul_mant_quart_in_1;


  logic [posit_pkg::EXP_COMBINED_FULL_L : 0]        adder_exp_full_out;
  logic [1:0] [posit_pkg::EXP_COMBINED_HALF_L : 0]  adder_exp_half_out;
  logic [3:0] [posit_pkg::EXP_COMBINED_QUART_L : 0] adder_exp_quart_out;

  logic [posit_pkg::MANT_FULL_L + 1 : 0]            adder_mant_full_out;
  logic [1 : 0] [posit_pkg::MANT_HALF_L + 1 : 0]    adder_mant_half_out;
  logic [3 : 0] [posit_pkg::MANT_QUART_L + 1 : 0]   adder_mant_quart_out;

  logic [posit_pkg::EXP_COMBINED_FULL_L : 0]        mult_exp_full_out;
  logic [1:0] [posit_pkg::EXP_COMBINED_HALF_L : 0]  mult_exp_half_out;
  logic [3:0] [posit_pkg::EXP_COMBINED_QUART_L : 0] mult_exp_quart_out;

  logic [posit_pkg::MANT_FULL_L + 1 : 0]            mult_mant_full_out;
  logic [1 : 0] [posit_pkg::MANT_HALF_L + 1 : 0]    mult_mant_half_out;
  logic [3 : 0] [posit_pkg::MANT_QUART_L + 1 : 0]   mult_mant_quart_out;
  
  logic [posit_pkg::EXP_COMBINED_FULL_L : 0]        pre_round_exp_full;
  logic [1:0] [posit_pkg::EXP_COMBINED_HALF_L : 0]  pre_round_exp_half;
  logic [3:0] [posit_pkg::EXP_COMBINED_QUART_L : 0] pre_round_exp_quart;

  logic [posit_pkg::MANT_FULL_L + 1 : 0]            pre_round_mant_full;
  logic [1 : 0] [posit_pkg::MANT_HALF_L + 1 : 0]    pre_round_mant_half;
  logic [3 : 0] [posit_pkg::MANT_QUART_L + 1 : 0]   pre_round_mant_quart;

  posit_pkg::exp_full_t         pre_pack_exp_full;
  posit_pkg::mant_full_t        pre_pack_mant_full;

  posit_pkg::exp_half_t   [1:0] pre_pack_exp_half;
  posit_pkg::mant_half_t  [1:0] pre_pack_mant_half;

  posit_pkg::exp_quart_t  [3:0] pre_pack_exp_quart;
  posit_pkg::mant_quart_t [3:0] pre_pack_mant_quart;

  assign pre_round_exp_full   = mul_en ? mult_exp_full_out   : adder_exp_full_out  ;
  assign pre_round_mant_full  = mul_en ? mult_mant_full_out  : adder_mant_full_out ;
            
  assign pre_round_exp_half   = mul_en ? mult_exp_half_out   : adder_exp_half_out  ;
  assign pre_round_mant_half  = mul_en ? mult_mant_half_out  : adder_mant_half_out ;
           
  assign pre_round_exp_quart  = mul_en ? mult_exp_quart_out  : adder_exp_quart_out ;
  assign pre_round_mant_quart = mul_en ? mult_mant_quart_out : adder_mant_quart_out;

  assign mul_exp_full_in_0   = mul_en ? exp_full_in_0   : '0;
  assign mul_mant_full_in_0  = mul_en ? mant_full_in_0  : '0;
  assign mul_exp_half_in_0   = mul_en ? exp_half_in_0   : '0;
  assign mul_mant_half_in_0  = mul_en ? mant_half_in_0  : '0;
  assign mul_exp_quart_in_0  = mul_en ? exp_quart_in_0  : '0;
  assign mul_mant_quart_in_0 = mul_en ? mant_quart_in_0 : '0;
  assign mul_exp_full_in_1   = mul_en ? exp_full_in_1   : '0;
  assign mul_mant_full_in_1  = mul_en ? mant_full_in_1  : '0;
  assign mul_exp_half_in_1   = mul_en ? exp_half_in_1   : '0;
  assign mul_mant_half_in_1  = mul_en ? mant_half_in_1  : '0;
  assign mul_exp_quart_in_1  = mul_en ? exp_quart_in_1  : '0;
  assign mul_mant_quart_in_1 = mul_en ? mant_quart_in_1 : '0;

  assign add_exp_full_in_0   = ~mul_en ? exp_full_in_0   : '0;
  assign add_mant_full_in_0  = ~mul_en ? mant_full_in_0  : '0;
  assign add_exp_half_in_0   = ~mul_en ? exp_half_in_0   : '0;
  assign add_mant_half_in_0  = ~mul_en ? mant_half_in_0  : '0;
  assign add_exp_quart_in_0  = ~mul_en ? exp_quart_in_0  : '0;
  assign add_mant_quart_in_0 = ~mul_en ? mant_quart_in_0 : '0;
  assign add_exp_full_in_1   = ~mul_en ? exp_full_in_1   : '0;
  assign add_mant_full_in_1  = ~mul_en ? mant_full_in_1  : '0;
  assign add_exp_half_in_1   = ~mul_en ? exp_half_in_1   : '0;
  assign add_mant_half_in_1  = ~mul_en ? mant_half_in_1  : '0;
  assign add_exp_quart_in_1  = ~mul_en ? exp_quart_in_1  : '0;
  assign add_mant_quart_in_1 = ~mul_en ? mant_quart_in_1 : '0;

  //===========================================
  //      Instances 
  //===========================================
  extract_fields #(.ES_L_32(ES_FULL_L), .ES_L_16(ES_HALF_L), .ES_L_8(ES_QUART_L)) EXTRACT_FIELDS_INS_0 (
    .clk    (clk),// for assertion

    .in     (in_0),
    .exp32  (exp_full_in_0),
    .mant32 (mant_full_in_0),

    .exp16  (exp_half_in_0),
    .mant16 (mant_half_in_0),

    .exp8   (exp_quart_in_0),
    .mant8  (mant_quart_in_0),

    .mode   (mode)
  );

  extract_fields #(.ES_L_32(ES_FULL_L), .ES_L_16(ES_HALF_L), .ES_L_8(ES_QUART_L)) EXTRACT_FIELDS_INS_1 (
    .clk    (clk),// for assertion

    .in     (in_1),
    .exp32  (exp_full_in_1),
    .mant32 (mant_full_in_1),

    .exp16  (exp_half_in_1),
    .mant16 (mant_half_in_1),

    .exp8   (exp_quart_in_1),
    .mant8  (mant_quart_in_1),

    .mode   (mode)
  );

  flt_adder_decomposable FLT_ADDER_DECOMPOSABLE_INS (
    .exp_full_in_0  (add_exp_full_in_0  ),
    .mant_full_in_0 (add_mant_full_in_0 ),

    .exp_half_in_0  (add_exp_half_in_0  ),
    .mant_half_in_0 (add_mant_half_in_0 ),

    .exp_quart_in_0 (add_exp_quart_in_0 ),
    .mant_quart_in_0(add_mant_quart_in_0),
 
    .exp_full_in_1  (add_exp_full_in_1  ),
    .mant_full_in_1 (add_mant_full_in_1 ),
 
    .exp_half_in_1  (add_exp_half_in_1  ),
    .mant_half_in_1 (add_mant_half_in_1 ),
 
    .exp_quart_in_1 (add_exp_quart_in_1 ),
    .mant_quart_in_1(add_mant_quart_in_1),
                                    
    .mode           (mode           ),
                                    
    .exp_full_out   (adder_exp_full_out   ),
    .exp_half_out   (adder_exp_half_out   ),
    .exp_quart_out  (adder_exp_quart_out  ),
                   
    .mant_full_out  (adder_mant_full_out  ),
    .mant_half_out  (adder_mant_half_out  ),
    .mant_quart_out (adder_mant_quart_out)
  );

  flt_multiplier_decomposable FLT_MULTIPLIER_DECOMPOSABLE_INS (
    .exp_full_in_0  (mul_exp_full_in_0  ),
    .mant_full_in_0 (mul_mant_full_in_0 ),

    .exp_half_in_0  (mul_exp_half_in_0  ),
    .mant_half_in_0 (mul_mant_half_in_0 ),

    .exp_quart_in_0 (mul_exp_quart_in_0 ),
    .mant_quart_in_0(mul_mant_quart_in_0),

    .exp_full_in_1  (mul_exp_full_in_1  ),
    .mant_full_in_1 (mul_mant_full_in_1 ),

    .exp_half_in_1  (mul_exp_half_in_1  ),
    .mant_half_in_1 (mul_mant_half_in_1 ),

    .exp_quart_in_1 (mul_exp_quart_in_1 ),
    .mant_quart_in_1(mul_mant_quart_in_1),
                                    
    .mode           (mode           ),
                                    
    .exp_full_out   (mult_exp_full_out   ),
    .exp_half_out   (mult_exp_half_out   ),
    .exp_quart_out  (mult_exp_quart_out  ),
                   
    .mant_full_out  (mult_mant_full_out  ),
    .mant_half_out  (mult_mant_half_out  ),
    .mant_quart_out (mult_mant_quart_out)
  );

 round_norm_overflow_underflow ROUND_NORM_OVERFLOW_UNDERFLOW_INS (
   .exp_full_in   (pre_round_exp_full),
   .exp_half_in   (pre_round_exp_half),
   .exp_quart_in  (pre_round_exp_quart),

   .mant_full_in  (pre_round_mant_full),
   .mant_half_in  (pre_round_mant_half),
   .mant_quart_in (pre_round_mant_quart),

   .exp_full_out  (pre_pack_exp_full  ),
   .mant_full_out (pre_pack_mant_full ),

   .exp_half_out  (pre_pack_exp_half  ),
   .mant_half_out (pre_pack_mant_half ),

   .exp_quart_out (pre_pack_exp_quart ),
   .mant_quart_out(pre_pack_mant_quart)

); 

  pack_fields PACK_FIELDS_INS (
    .out       (out),

    .exp_full  (pre_pack_exp_full  ),
    .mant_full (pre_pack_mant_full ),

    .exp_half  (pre_pack_exp_half  ),
    .mant_half (pre_pack_mant_half ),

    .exp_quart (pre_pack_exp_quart ),
    .mant_quart(pre_pack_mant_quart),

    .mode      (mode)
  ); 


  assert property (@(posedge clk) (in_0 != '1)) else $warning("%h", in_0);
  assert property (@(posedge clk) (in_1 != '1)) else $warning("%h", in_1);
endmodule

`endif //POSIT_ARITH_UNIT_DEF

