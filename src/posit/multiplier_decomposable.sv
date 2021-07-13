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
  input  unsigned [EACH_PART_LEN * N_PARTS - 1 : 0] in0,
  input  unsigned [EACH_PART_LEN * N_PARTS - 1 : 0] in1,
  
  input  unsigned [PRECISION_CONFIG_L - 1 : 0] mode,
  output unsigned  [2 * EACH_PART_LEN * N_PARTS - 1 : 0] out_full,
  output unsigned  [1: 0] [EACH_PART_LEN * N_PARTS - 1 : 0] out_half,
  output unsigned  [3: 0] [EACH_PART_LEN * 2 - 1 : 0] out_quarter

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

  logic unsigned [2 * EACH_PART_LEN - 1 : 0] partial_prods[N_PARTS - 1 : 0] [N_PARTS - 1 : 0];
  
  logic unsigned [2 * EACH_PART_LEN - 1 : 0] partial_prods_0_0;
  logic unsigned [2 * EACH_PART_LEN - 1 : 0] partial_prods_0_1;
  logic unsigned [2 * EACH_PART_LEN - 1 : 0] partial_prods_1_0;
  logic unsigned [2 * EACH_PART_LEN - 1 : 0] partial_prods_1_1;
  logic unsigned [2 * EACH_PART_LEN - 1 : 0] partial_prods_2_2;
  logic unsigned [2 * EACH_PART_LEN - 1 : 0] partial_prods_2_3;
  logic unsigned [2 * EACH_PART_LEN - 1 : 0] partial_prods_3_2;
  logic unsigned [2 * EACH_PART_LEN - 1 : 0] partial_prods_3_3;

  logic unsigned [EACH_PART_LEN - 1 : 0] gated_in0[N_PARTS - 1 : 0] [N_PARTS - 1 : 0];
  logic unsigned [EACH_PART_LEN - 1 : 0] gated_in1[N_PARTS - 1 : 0] [N_PARTS - 1 : 0];

  logic unsigned [2 * EACH_PART_LEN * N_PARTS - 1 : 0]    out_full_pre;

  logic unsigned  [EACH_PART_LEN * N_PARTS - 1 : 0] out_half_pre[3:0];
  
  logic unsigned  [EACH_PART_LEN * N_PARTS - 1 : 0] out_half_pre_0_0;
  logic unsigned  [EACH_PART_LEN * N_PARTS - 1 : 0] out_half_pre_0_1;
  logic unsigned  [EACH_PART_LEN * N_PARTS - 1 : 0] out_half_pre_3_0;
  logic unsigned  [EACH_PART_LEN * N_PARTS - 1 : 0] out_half_pre_3_1;

  logic unsigned [3: 0] [EACH_PART_LEN * 2 - 1 : 0]       out_quarter_pre;

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

  assign out_half_pre[0] = { 16'b0, partial_prods[0][0]} + { 8'b0, partial_prods[0][1], 8'b0} + { 8'b0, partial_prods[1][0], 8'b0} + {partial_prods[1][1], 16'b0};
  assign out_half_pre[3] = { 16'b0, partial_prods[2][2]} + { 8'b0, partial_prods[2][3], 8'b0} + { 8'b0, partial_prods[3][2], 8'b0} + {partial_prods[3][3], 16'b0};

  assign out_half_pre[1] = {gated_in0[1][0], gated_in0[0][0]} * {gated_in1[0][3], gated_in1[0][2]};
  assign out_half_pre[2] = {gated_in0[3][0], gated_in0[2][0]} * {gated_in1[0][1], gated_in1[0][0]};

  assign out_full_pre = {32'b0 , out_half_pre[0]} + {16'b0, out_half_pre[1], 16'b0} +
                        {16'b0, out_half_pre[2], 16'b0} + {out_half_pre[3] , 32'b0};

  assign out_full = out_full_pre;
  assign out_half[0]= out_half_pre[0];
  assign out_half[1]= out_half_pre[3];
  assign out_quarter= out_quarter_pre;

endmodule

`endif //MULTIPLIER_DECOMPOSABLE_DEF
