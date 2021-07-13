//=======================================================================
// Created by         : KU Leuven
// Filename           : multipler_decomposable.sv
// Author             : Nimish Shah
// Created On         : 2019-12-22 15:44
// Last Modified      : 
// Update Count       : 2019-12-22 15:44
// Description        : 
//                      
//=======================================================================

`ifndef MULTIPLIER_DECOMPOSABLE_DEF
  `define MULTIPLIER_DECOMPOSABLE_DEF

  `include "../common.sv"

module multiplier_decomposable  #(parameter EACH_PART_LEN= 8, N_PARTS= 4) (
  // implementation non parameterizable 
  input [EACH_PART_LEN * N_PARTS - 1 : 0] in0,
  input [EACH_PART_LEN * N_PARTS - 1 : 0] in1,
  
  input [PRECISION_CONFIG_L - 1 : 0] mode,
  output [2 * EACH_PART_LEN * N_PARTS - 1 : 0] out_full,
  output [1: 0] [EACH_PART_LEN * N_PARTS - 1 : 0] out_half,
  output [3: 0] [EACH_PART_LEN * 2 - 1 : 0] out_quarter

); 
//                                                                  
//                                   in1                           
//                                                                 
//                                    j-axis                       
//                    3                                        0   
//                  +---------------------------------------------+
//               3  |                                             |
//                  |                                             |
//                  |                                             |
//                  |                                             |
//                  |                                             |
//                  |                                             |
// in0              |                                             |
//                  |                                             |
// i-axis           |                  multiplier                 |
//                  |                                             |
//                  |                                             |
//                  |                                             |
//                  |                                             |
//                  |                                             |
//                  |                                             |
//                  |                                             |
//               0  |                                             |
//                  +---------------------------------------------+
//                   3                                           0 
//                                                                 
//                                      output                      
//
                                                                 
                                                                 
//                   3                                         0   
//                                                                 
//              3   +---------------------+                        
//                  |                     |                        
//                  |                     |                        
//                  |                     |                        
//                  |                     |                        
//                  |                     |                        
//                  |                     |                        
//                  +---------------------+---------------------+  
//                                        |                     |  
//                                        |                     |  
//                                        |                     |  
//                                        |                     |  
//                                        |                     |  
//                                        |                     |  
//               0                        +---------------------+  
//                                                                 
//                    3                                            
//                                                             0   
//              3   +----------+                                   
//                  |          |                                   
//                  |          |                                   
//                  |          |                                   
//                  +----------+----------+                        
//                             |          |                        
//                             |          |                        
//                             |          |                        
//                             +----------+----------+             
//                                        |          |             
//                                        |          |             
//                                        |          |             
//                                        +----------+----------+  
//                                                   |          |  
//                                                   |          |  
//                                                   |          |  
//              0                                    +----------+  
  
  initial assert (N_PARTS == 4);

  localparam TOTAL_LEN= EACH_PART_LEN * N_PARTS;

  logic [2 * EACH_PART_LEN - 1 : 0] partial_prods[N_PARTS - 1 : 0] [N_PARTS - 1 : 0];
  
  logic [2 * EACH_PART_LEN - 1 : 0] partial_prods_0_0;
  logic [2 * EACH_PART_LEN - 1 : 0] partial_prods_0_1;
  logic [2 * EACH_PART_LEN - 1 : 0] partial_prods_1_0;
  logic [2 * EACH_PART_LEN - 1 : 0] partial_prods_1_1;
  logic [2 * EACH_PART_LEN - 1 : 0] partial_prods_2_2;
  logic [2 * EACH_PART_LEN - 1 : 0] partial_prods_2_3;
  logic [2 * EACH_PART_LEN - 1 : 0] partial_prods_3_2;
  logic [2 * EACH_PART_LEN - 1 : 0] partial_prods_3_3;

  logic [N_PARTS * EACH_PART_LEN - 1 : 0] gated_in0;
  logic [N_PARTS * EACH_PART_LEN - 1 : 0] gated_in1;

  logic [2 * EACH_PART_LEN * N_PARTS - 1 : 0]    out_full_pre;

  logic  [EACH_PART_LEN * N_PARTS - 1 : 0] out_half_pre[3:0];
  
  logic  [EACH_PART_LEN * N_PARTS - 1 : 0] out_half_pre_0_0;
  logic  [EACH_PART_LEN * N_PARTS - 1 : 0] out_half_pre_0_1;
  logic  [EACH_PART_LEN * N_PARTS - 1 : 0] out_half_pre_3_0;
  logic  [EACH_PART_LEN * N_PARTS - 1 : 0] out_half_pre_3_1;

  logic [3: 0] [EACH_PART_LEN * 2 - 1 : 0]       out_quarter_pre;

  // input gating
  always_comb begin
    for (integer i=0; i< N_PARTS; i=i+1) begin
      for (integer j=0; j< N_PARTS; j=j+1) begin
        gated_in0 [i][j] = '0;
        gated_in1 [i][j] = '0;
      end
    end

    case (mode) 
      pe_pkg::PRECISION_CONFIG_32B : begin 
        for (integer i=0; i< N_PARTS; i=i+1) begin
          for (integer j=0; j< N_PARTS; j=j+1) begin
            gated_in0 [i][j] = in0[i*EACH_PART_LEN +: EACH_PART_LEN];
            gated_in1 [i][j] = in1[j*EACH_PART_LEN +: EACH_PART_LEN];
          end
        end
      end

      pe_pkg::PRECISION_CONFIG_16B : begin 
        for (integer i=0; i< N_PARTS; i=i+1) begin
          for (integer j=0; j< N_PARTS; j=j+1) begin

            if (i < 2 && j < 2) begin
              gated_in0 [i][j] = in0[i*EACH_PART_LEN +: EACH_PART_LEN];
              gated_in1 [i][j] = in1[j*EACH_PART_LEN +: EACH_PART_LEN];
            end
            if (i >= 2 && j >= 2) begin
              gated_in0 [i][j] = in0[i*EACH_PART_LEN +: EACH_PART_LEN];
              gated_in1 [i][j] = in1[j*EACH_PART_LEN +: EACH_PART_LEN];
            end
          end
        end
      end

      pe_pkg::PRECISION_CONFIG_8B : begin 
        for (integer i=0; i< N_PARTS; i=i+1) begin
          for (integer j=0; j< N_PARTS; j=j+1) begin

            if (i == j) begin
              gated_in0 [i][j] = in0[i*EACH_PART_LEN +: EACH_PART_LEN];
              gated_in1 [i][j] = in1[j*EACH_PART_LEN +: EACH_PART_LEN];
            end
          end
        end
      end
    endcase
  end

  // partial product generation
  always_comb begin
    for (integer i=0; i< N_PARTS; i=i+1) begin
      for (integer j=0; j< N_PARTS; j=j+1) begin
        partial_prods[i][j] = gated_in0[i][j] * gated_in1[i][j];
      end
    end
  end

  // output gen
  always_comb begin
    out_quarter_pre = 'x;
    foreach ( out_quarter_pre[i]) begin
      out_quarter_pre[i] = partial_prods[i][i];
    end
  end

//  assign out_half_pre[0] = (partial_prods[0][0] + (partial_prods[0][1] << EACH_PART_LEN)) +
//                           ((partial_prods[1][0] + (partial_prods[1][1] << EACH_PART_LEN)) << EACH_PART_LEN);
//
//  assign out_half_pre[1] = (partial_prods[2][0] + (partial_prods[3][0] << EACH_PART_LEN)) +
//                           ((partial_prods[2][1] + (partial_prods[3][1] << EACH_PART_LEN)) << EACH_PART_LEN);
//
//  assign out_half_pre[2] = (partial_prods[0][2] + (partial_prods[1][2] << EACH_PART_LEN)) +
//                           ((partial_prods[0][3] + (partial_prods[1][3] << EACH_PART_LEN)) << EACH_PART_LEN);
//
//  assign out_half_pre[3] = (partial_prods[2][2] + (partial_prods[2][3] << EACH_PART_LEN)) +
//                           ((partial_prods[3][2] + (partial_prods[3][3] << EACH_PART_LEN)) << EACH_PART_LEN);

  assign partial_prods_0_0 = gated_in0[0][0] * gated_in1[0][0];
  assign partial_prods_0_1 = gated_in0[0][1] * gated_in1[0][1];
  assign partial_prods_1_0 = gated_in0[1][0] * gated_in1[1][0];
  assign partial_prods_1_1 = gated_in0[1][1] * gated_in1[1][1];
  assign partial_prods_2_2 = gated_in0[2][2] * gated_in1[2][2];
  assign partial_prods_2_3 = gated_in0[2][3] * gated_in1[2][3];
  assign partial_prods_3_2 = gated_in0[3][2] * gated_in1[3][2];
  assign partial_prods_3_3 = gated_in0[3][3] * gated_in1[3][3];

  assign out_half_pre[0] = partial_prods_0_0 + {partial_prods_0_1, 8'b0} + {partial_prods_1_0, 8'b0} + {partial_prods_1_1, 16'b0};
  assign out_half_pre[3] = partial_prods_2_2 + {partial_prods_2_3, 8'b0} + {partial_prods_3_2, 8'b0} + {partial_prods_3_3, 16'b0};

//  assign out_half_pre[0] = (partial_prods_0_0 + {partial_prods_0_1, 8'b0}) +
//                           {(partial_prods_1_0 + {partial_prods_1_1, 8'b0}), 8'b0};
//
//  assign out_half_pre[3] = (partial_prods_2_2 + {partial_prods_3_2, 8'b0}) +
//                           {(partial_prods_2_3 + {partial_prods_3_3, 8'b0}), 8'b0};

//  assign out_half_pre[0] = (partial_prods[0][0] + {partial_prods[0][1], 8'b0}) +
//                           {(partial_prods[1][0] + {partial_prods[1][1], 8'b0}), 8'b0};

//  assign out_half_pre[1] = (partial_prods[2][0] + {partial_prods[3][0], {EACH_PART_LEN{1'b0}}}) +
//                           {(partial_prods[2][1] + {partial_prods[3][1], {EACH_PART_LEN{1'b0}}}), {EACH_PART_LEN{1'b0}}};
//
//  assign out_half_pre[2] = (partial_prods[0][2] + {partial_prods[1][2], {EACH_PART_LEN{1'b0}}}) +
//                           {(partial_prods[0][3] + {partial_prods[1][3], {EACH_PART_LEN{1'b0}}}), {EACH_PART_LEN{1'b0}}};

//  assign out_half_pre[3] = (partial_prods[2][2] + {partial_prods[3][2], 8'b0}) +
//                           {(partial_prods[2][3] + {partial_prods[3][3], 8'b0}), 8'b0};

/*
  assign out_half_pre[0] = in0[0 +: 16] * in1[0 +: 16];
  assign out_half_pre[1] = in0[0 +: 16] * in1[16 +: 16];
  assign out_half_pre[2] = in0[16 +: 16] * in1[0 +: 16];
  assign out_half_pre[3] = in0[16 +: 16] * in1[16 +: 16];
*/

  //assign out_half_pre[0] = {gated_in0[1][0], gated_in0[0][0]} * {gated_in1[0][1], gated_in1[0][0]};
  assign out_half_pre[1] = {gated_in0[1][0], gated_in0[0][0]} * {gated_in1[0][3], gated_in1[0][2]};
  assign out_half_pre[2] = {gated_in0[3][0], gated_in0[2][0]} * {gated_in1[0][1], gated_in1[0][0]};
  //assign out_half_pre[3] = {gated_in0[3][0], gated_in0[2][0]} * {gated_in1[0][3], gated_in1[0][2]};

//  assign out_full_pre = (out_half_pre[0] + (out_half_pre[1] << 2*EACH_PART_LEN)) +
//                        ((out_half_pre[2] + (out_half_pre[3] << 2* EACH_PART_LEN)) << 2*EACH_PART_LEN);
  
//  assign out_full_pre = (out_half_pre[0] + {out_half_pre[1], {2*EACH_PART_LEN{1'b0}}}) +
//                        {(out_half_pre[2] + {out_half_pre[3] , {2* EACH_PART_LEN{1'b0}}}), {2*EACH_PART_LEN{1'b0}}};

  assign out_full_pre = (out_half_pre[0] + {out_half_pre[1], 16'b0}) +
                        {(out_half_pre[2] + {out_half_pre[3] , 16'b0}), 16'b0};

  assign out_full = out_full_pre;
  assign out_half[0]= out_half_pre[0];
  assign out_half[1]= out_half_pre[3];
  assign out_quarter= out_quarter_pre;

endmodule

`endif //MULTIPLIER_DECOMPOSABLE_DEF
