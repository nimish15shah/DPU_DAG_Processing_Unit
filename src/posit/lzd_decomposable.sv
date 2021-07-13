//=======================================================================
// Created by         : KU Leuven
// Filename           : lzd_decomposable.sv
// Author             : Nimish Shah
// Created On         : 2019-12-20 16:21
// Last Modified      : 
// Update Count       : 2019-12-20 16:21
// Description        : 
//                      
//=======================================================================

`ifndef LZD_DECOMPOSABLE_DEF
  `define LZD_DECOMPOSABLE_DEF

  `include "priority_encoder.sv"

module lzd_decomposable #(parameter MAX_BITS = 32) (
  input [MAX_BITS - 1 : 0] in,
  output [$clog2(MAX_BITS) - 1 : 0]          out_full,
  output                                     all_ones_full,

  output [1 : 0][$clog2(MAX_BITS/2) - 1 : 0] out_half,
  output [1 : 0]                             all_ones_half,

  output [3 : 0][$clog2(MAX_BITS/4) - 1 : 0] out_quarter,
  output [3 : 0]                             all_ones_quarter
); 

// MSB highest priority

                                                                                                                        
//      quarter input                   quarter input              quarter input                   quarter input          
//            |                               |                          |                               |                
//            |                               |                          |                               |                
//            v                               v                          v                               v                
//+----------------------+        +----------------------+   +----------------------+        +----------------------+     
//|                      |        |                      |   |                      |        |                      |     
//|   priority encoder   |        |   priority encoder   |   |   priority encoder   |        |   priority encoder   |     
//|     (quarter len)    |        |     (quarter len)    |   |     (quarter len)    |        |     (quarter len)    |     
//|                      |        |                      |   |                      |        |                      |     
//+----------------------+        +----------------------+   +----------------------+        +----------------------+     
//      |          |                    |          |               |          |                    |          |           
//      |          |                    |          |               |          |                    |          |           
//      v          v                    v          v               v          v                    v          v           
//    all      out quarter            all      out quarter       all      out quarter            all      out quarter     
//    ones        \                   ones      /--              ones        \                   ones      /--            
//      |          -\                       /---                   |          -\                       /---               
//      |            -\                 /---                       |            -\                 /---                   
//      |              >             <--                           |              >             <--                       
//      |         1:xxx            0:xxx                           |         1:xxx            0:xxx                       
//      |                                                          |                                                      
//      |            +-------------+                               |            +-------------+                           
//      |            |             |                               |            |             |                           
//      +----------> |    mux      |                               +----------> |    mux      |                           
//                   |             |                                            |             |                           
//                   +-------------+                                            +-------------+                           
//                          |                                                          |                                  
//                          |                                                          |                                  
//                          v                                                          v                                  
//                     out half--\                                             /--out half                                
//                                ----\                                   /----                                           
//                                     ---\                           /---                                                
//                                         -->                     <--                                                    
//                                         1:xxxx               0:xxxx                                                    
//                                                                                                                        
//                                               +-------------+                                                          
//                                               |             |                                                          
//                             if both    ------>|    mux      |                                                          
//                             first quarter     |             |                                                          
//                             are all ones      +-------------+                                                          
//                                                      |                                                                 
//                                                      |                                                                 
//                                                      v                                                                 
//                                                     out full                                                           

  
  //===========================================
  //      Signals
  //===========================================
  localparam OUT_L = $clog2(MAX_BITS);

  logic [OUT_L -1 : 0] out_full_pre;
  logic all_ones_full_pre;

  logic [1: 0][OUT_L -2 : 0] out_half_pre;
  logic [1 : 0] all_ones_half_pre;

  logic [3: 0][OUT_L -3 : 0] out_quarter_pre;
  logic [3:0] all_ones_quarter_pre;
  
  assign all_ones_half_pre[1]= all_ones_quarter_pre[3] & all_ones_quarter_pre[2];
  assign all_ones_half_pre[0]= all_ones_quarter_pre[1] & all_ones_quarter_pre[0];

  assign all_ones_full_pre = all_ones_half_pre[1] & all_ones_half_pre[0];
  //===========================================
  //      Instances 
  //===========================================
  generate
    genvar quarter_i;
    for (quarter_i=0; quarter_i< 4; quarter_i=quarter_i+1) begin: quarter_loop
      
      priority_encoder_active_low #(.N_IN(MAX_BITS/4)) 
        PRIORITY_ENCODER_ACTIVE_LOW_INS
      (
        .in  (in[quarter_i*(MAX_BITS/4) +: MAX_BITS/4]),
        .out (out_quarter_pre[quarter_i]),

        .all_ones (all_ones_quarter_pre[quarter_i])
      );
    end
  endgenerate

  //===========================================
  //      Combinational 
  //===========================================
  always_comb begin
    if (all_ones_quarter_pre[3] == 0) begin
      out_half_pre[1] = {1'b1, out_quarter_pre[3]};
    end else begin
      out_half_pre[1] = {1'b0, out_quarter_pre[2]};
    end
  end

  always_comb begin
    if (all_ones_quarter_pre[1] == 0) begin
      out_half_pre[0] = {1'b1, out_quarter_pre[1]};
    end else begin
      out_half_pre[0] = {1'b0, out_quarter_pre[0]};
    end
  end
  
  always_comb begin
    if (all_ones_half_pre[1] == 0) begin
      out_full_pre = {1'b1, out_half_pre[1]};
    end else begin
      out_full_pre = {1'b0, out_half_pre[0]};
    end
  end

  assign out_full        = out_full_pre;
  assign all_ones_full   = all_ones_full_pre;

  assign out_half        = out_half_pre;
  assign all_ones_half   = all_ones_half_pre;

  assign out_quarter     = out_quarter_pre;
  assign all_ones_quarter= all_ones_quarter_pre;

endmodule


`endif //LZD_DECOMPOSABLE_DEF

