//=======================================================================
// Created by         : KU Leuven
// Filename           : shifter_decomposable.sv
// Author             : Nimish Shah
// Created On         : 2019-12-22 11:40
// Last Modified      : 
// Update Count       : 2019-12-22 11:40
// Description        : 
//                      
//=======================================================================

`ifndef SHIFTER_DECOMPOSABLE_DEF
  `define SHIFTER_DECOMPOSABLE_DEF

  `include "../common.sv"

// Set ARITH_SHIFT to 1, for sign extension
// If ARITH_SHIFT is set to 0, EXTENSION_BIT indicates if to pad with 0s or 1s
module left_shift_decomposable #(parameter ARITH_SHIFT= 0, EXTENSION_BIT= 0) (

  input [31: 0] in,

  input [3:0] [4:0] shift_val,
  input full_shift,

  input [PRECISION_CONFIG_L - 1 : 0] mode,

  output [31 : 0] out
);
  
  localparam EACH_SHIFTER_LEN= 8;
  localparam N_SHIFTER = 4;
  localparam TOTAL_LEN= N_SHIFTER * EACH_SHIFTER_LEN;
  localparam N_STAGES = $clog2(TOTAL_LEN);

  logic [N_SHIFTER -1 : 0]         extend_0, extend_0_gated;
  logic [N_SHIFTER -1 : 0] [1 : 0] extend_1, extend_1_gated;
  logic [N_SHIFTER -1 : 0] [3 : 0] extend_2, extend_2_gated;
  logic [N_SHIFTER -1 : 0] [7 : 0] extend_3, extend_3_gated;
  logic [N_SHIFTER -1 : 0] [15 : 0]extend_4, extend_4_gated;

  logic [N_SHIFTER -1 : 0] [N_STAGES -1 : 0] [EACH_SHIFTER_LEN - 1 : 0] out_per_shifter;
  
  logic [TOTAL_LEN - 1: 0] out_pre;

  generate
    genvar shifter_i;
    for (shifter_i=0; shifter_i<N_SHIFTER; shifter_i=shifter_i+1) begin: shifter_loop

      if (shifter_i > 0) begin: shifter_last_bit_if
        assign extend_0[shifter_i] = in[shifter_i*EACH_SHIFTER_LEN - 1];
        assign extend_1[shifter_i] = out_per_shifter[shifter_i-1][0][EACH_SHIFTER_LEN - 1 -: 2];
        assign extend_2[shifter_i] = out_per_shifter[shifter_i-1][1][EACH_SHIFTER_LEN - 1 -: 4];
        assign extend_3[shifter_i] = out_per_shifter[shifter_i-1][2][EACH_SHIFTER_LEN - 1 -: 8];
      end else begin: shifter_last_bit_else
        if (ARITH_SHIFT == 0) begin: block_0
          assign extend_0[shifter_i] = EXTENSION_BIT ? '1 : '0;
          assign extend_1[shifter_i] = EXTENSION_BIT ? '1 : '0; 
          assign extend_2[shifter_i] = EXTENSION_BIT ? '1 : '0;
          assign extend_3[shifter_i] = EXTENSION_BIT ? '1 : '0;
        end else begin: block_1
//          assign extend_0[shifter_i] = in[shifter_i*EACH_SHIFTER_LEN] ? '1 : '0;
//          assign extend_1[shifter_i] = in[shifter_i*EACH_SHIFTER_LEN] ? '1 : '0; 
//          assign extend_2[shifter_i] = in[shifter_i*EACH_SHIFTER_LEN] ? '1 : '0;
//          assign extend_3[shifter_i] = in[shifter_i*EACH_SHIFTER_LEN] ? '1 : '0;
          assign extend_0[shifter_i] = in[0] ? '1 : '0;
          assign extend_1[shifter_i] = in[0] ? '1 : '0; 
          assign extend_2[shifter_i] = in[0] ? '1 : '0;
          assign extend_3[shifter_i] = in[0] ? '1 : '0;
        end
      end

      if (shifter_i > 1) begin: shifter_second_last_bit_if
        assign extend_4[shifter_i] = {out_per_shifter[shifter_i-1][3],out_per_shifter[shifter_i-2][3]};
      end else begin: shifter_second_last_bit_else
        if (ARITH_SHIFT == 0) begin: block_2
          assign extend_4[shifter_i] = EXTENSION_BIT ? '1 : '0;
        end else begin: block_3
          assign extend_4[shifter_i] = in[0] ? '1 : '0;
        end
      end

      left_shift_building_block #(.LEN(EACH_SHIFTER_LEN)) LEFT_SHIFT_BUILDING_BLOCK_INS (
        .in      (in[shifter_i * EACH_SHIFTER_LEN +: EACH_SHIFTER_LEN]),

        .extend_0 (extend_0_gated[shifter_i] ),
        .extend_1 (extend_1_gated[shifter_i] ),
        .extend_2 (extend_2_gated[shifter_i] ),
        .extend_3 (extend_3_gated[shifter_i] ),
        .extend_4 (extend_4_gated[shifter_i] ),

        .shift_val(shift_val     [shifter_i]),
        .out      (out_per_shifter[shifter_i])
      );

    end
  endgenerate

  always_comb begin
    extend_0_gated = extend_0;
    extend_1_gated = extend_1;
    extend_2_gated = extend_2;
    extend_3_gated = extend_3;
    extend_4_gated = extend_4;
    
    // break in middle
    if (mode == pe_pkg::PRECISION_CONFIG_16B) begin
      if (ARITH_SHIFT == 0) begin
        extend_4_gated = EXTENSION_BIT ? '1: '0;
        extend_3_gated[2] = EXTENSION_BIT ? '1: '0;
        extend_2_gated[2] = EXTENSION_BIT ? '1: '0;
        extend_1_gated[2] = EXTENSION_BIT ? '1: '0;
        extend_0_gated[2] = EXTENSION_BIT ? '1: '0;
      end else begin
        foreach ( extend_4_gated[i]) begin
          extend_4_gated[i] = in[(i/2) * 2 * EACH_SHIFTER_LEN] ? '1: '0;
        end
        extend_3_gated[2] = in[2*EACH_SHIFTER_LEN] ? '1: '0;
        extend_2_gated[2] = in[2*EACH_SHIFTER_LEN] ? '1: '0;
        extend_1_gated[2] = in[2*EACH_SHIFTER_LEN] ? '1: '0;
        extend_0_gated[2] = in[2*EACH_SHIFTER_LEN] ? '1: '0;
      end
      
    end

    if (mode == pe_pkg::PRECISION_CONFIG_8B) begin
        if (ARITH_SHIFT == 0) begin
          extend_4_gated = EXTENSION_BIT ? '1: '0;
          extend_3_gated = EXTENSION_BIT ? '1: '0;
          extend_2_gated = EXTENSION_BIT ? '1: '0;
          extend_1_gated = EXTENSION_BIT ? '1: '0;
          extend_0_gated = EXTENSION_BIT ? '1: '0;
        end else begin
          foreach ( extend_4_gated[i]) begin
            extend_4_gated[i] = in[i * EACH_SHIFTER_LEN] ? '1: '0;
            extend_3_gated[i] = in[i * EACH_SHIFTER_LEN] ? '1: '0;
            extend_2_gated[i] = in[i * EACH_SHIFTER_LEN] ? '1: '0;
            extend_1_gated[i] = in[i * EACH_SHIFTER_LEN] ? '1: '0;
            extend_0_gated[i] = in[i * EACH_SHIFTER_LEN] ? '1: '0;
          end
        end
    end

  end

  // output
  always_comb begin
    if (full_shift == 0) begin
      foreach ( out_per_shifter[i]) begin
        out_pre[i*EACH_SHIFTER_LEN +: EACH_SHIFTER_LEN] = out_per_shifter[i][N_STAGES-1];
      end
    end else begin
      out_pre = EXTENSION_BIT ? '1 : '0;
    end
  end
  
  assign out = out_pre;

endmodule


module left_shift_building_block #(parameter LEN= 8) (
  // MAX shift is not parameterizable yet

  input [LEN - 1 : 0] in,
  
  input extend_0,
  input [1 : 0] extend_1,
  input [3 : 0] extend_2,
  input [7 : 0] extend_3,
  input [15 : 0] extend_4,

  input [4: 0] shift_val,

  output [4: 0][LEN - 1 : 0] out
); 
  
  localparam N_STAGES= 5;

  logic [N_STAGES -1 : 0][LEN - 1 : 0] out_pre;

  //===========================================
  //      Instances 
  //===========================================
  left_shift_fixed #( .IN_LEN(LEN+1), .OUT_LEN(LEN), .SHIFT_VAL(1)) LEFT_SHIFT_FIXED_INS_0 (
    .in  ({in, extend_0}),  .out (out_pre[0]),   .shift_en (shift_val[0]) );

  left_shift_fixed #( .IN_LEN(LEN+2), .OUT_LEN(LEN), .SHIFT_VAL(2)) LEFT_SHIFT_FIXED_INS_1 (
    .in  ({out_pre[0], extend_1}),  .out (out_pre[1]),   .shift_en (shift_val[1]) );

  left_shift_fixed #( .IN_LEN(LEN+4), .OUT_LEN(LEN), .SHIFT_VAL(4)) LEFT_SHIFT_FIXED_INS_2 (
    .in  ({out_pre[1], extend_2}),  .out (out_pre[2]),   .shift_en (shift_val[2]) );

  left_shift_fixed #( .IN_LEN(LEN+8), .OUT_LEN(LEN), .SHIFT_VAL(8)) LEFT_SHIFT_FIXED_INS_3 (
    .in  ({out_pre[2], extend_3}),  .out (out_pre[3]),   .shift_en (shift_val[3]) );

  left_shift_fixed #( .IN_LEN(LEN+16), .OUT_LEN(LEN), .SHIFT_VAL(16)) LEFT_SHIFT_FIXED_INS_4 (
    .in  ({out_pre[3], extend_4}),  .out (out_pre[4]),   .shift_en (shift_val[4]) );

  assign out[0] = out_pre[0];
  assign out[1] = out_pre[1];
  assign out[2] = out_pre[2];
  assign out[3] = out_pre[3];
  assign out[4] = out_pre[4];

endmodule


module left_shift_fixed #(parameter IN_LEN= 8, OUT_LEN= 8, SHIFT_VAL= 1) (
  // IN_LEN can be >= OUT_LEN, but not smaller than
  input [IN_LEN - 1 : 0] in,
  output [OUT_LEN - 1 : 0] out,

  input shift_en
); 


// Left shift towards MSB by SHIFT_VAL if shift_en true
  
  logic [OUT_LEN - 1 : 0] out_pre;
  logic [IN_LEN - 1 : 0] shifted;

  assign shifted = in << SHIFT_VAL;

  always_comb begin
    if (shift_en) begin
      out_pre = shifted[IN_LEN - 1 -: OUT_LEN];
    end else begin
      out_pre = in[IN_LEN - 1 -: OUT_LEN];
    end
  end
  
  assign out = out_pre;
endmodule

module right_shift_decomposable #(parameter ARITH_SHIFT= 0, EXTENSION_BIT= 0)(
  input [31: 0] in,
  input [3:0] [4:0] shift_val,
  input full_shift,
  input [PRECISION_CONFIG_L - 1 : 0] mode,
  output [31 : 0] out
); 

  logic [3:0] [4:0] shift_val_reversed;
  logic [31: 0] in_reversed;
  logic [31: 0] out_reversed, out_pre;
  
  /*
  always_comb begin
    case (mode) 
      pe_pkg::PRECISION_CONFIG_32B : begin 
        foreach ( in_reversed[i]) begin
          in_reversed [i] = in[31 - i];
          out_pre [i] = out_reversed[31 - i];
        end
      end
      pe_pkg::PRECISION_CONFIG_16B : begin 
        for (integer i=0; i< 2; i=i+1) begin
          for (integer j=0; j< 16; j=j+1) begin
            in_reversed [i*16 + j] = in[i*16 + 15 - j];
            out_pre [i*16 + j] = out_reversed[i*16 + 15 - j];
          end
        end
      end
      pe_pkg::PRECISION_CONFIG_8B : begin 
        for (integer i=0; i< 4; i=i+1) begin
          for (integer j=0; j< 8; j=j+1) begin
            in_reversed [i*8 + j] = in[i*8 + 7 - j];
            out_pre [i*8 + j] = out_reversed[i*8 + 7 - j];
          end
        end
      end
    endcase
  end
  */

  always_comb begin
    foreach ( in_reversed[i]) begin
      in_reversed [i] = in[31 - i];
      out_pre [i] = out_reversed[31 - i];
    end
    foreach ( shift_val_reversed[j]) begin
      shift_val_reversed[j] = shift_val[3-j];
    end
  end

  left_shift_decomposable #(.ARITH_SHIFT(ARITH_SHIFT), .EXTENSION_BIT(EXTENSION_BIT)) LEFT_SHIFT_DECOMPOSABLE_INS(
    .in       (in_reversed),
    .shift_val(shift_val_reversed),
    .full_shift (full_shift),
    .mode     (mode),
    .out      (out_reversed)
  );
  
  assign out = out_pre;
endmodule


`endif //SHIFTER_DECOMPOSABLE_DEF
