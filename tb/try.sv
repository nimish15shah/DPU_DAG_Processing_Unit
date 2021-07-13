`include "shifter_decomposable.sv"
`include "posit_arith_unit.sv"

module test (
  ); 
  
  
  logic  [31: 0] in, in_1, in_0;
  logic  [31 : 0] in_reversed;

  logic  [3:0] [4:0] shift_val;

  logic  [PRECISION_CONFIG_L - 1 : 0] mode;

  logic  [31 : 0] out;
  
  logic [63 : 0] out_full;
  logic [31 : 0] out_half, out_posit;

  right_shift_decomposable #(.EXTENSION_BIT(0), .ARITH_SHIFT(1)) INST (
    //.in       (in_reversed ),
    .in       (in ),
    .shift_val(shift_val),
    .full_shift (1'b0),
    .mode     (mode     ),
    .out      (out      )
  );
  
  posit_arith_unit POSIT_ARITH_UNIT_INS (
    .clk (0), // for assertion

    .in_0(in_0),
    .in_1(in_1),
    .out(out_posit),

    .mode(mode),
    .mul_en(1'b0) // if 0 then add is enabled
  );

  initial begin
    $dumpfile("out/dump.vcd"); 
    $dumpvars;
    $dumpon;

    //in = 32'hAAAA_AAAA;
    //in = 32'h5555_5555;
    //in = 32'hFFFF_0000;
    //in = 32'h0000_FFFF;
    in = 32'h7070_7070;
    in_0 = 32'h8001_FEFE;
    in_1 = 32'hc001_0101;

    foreach (in[i]) begin
      in_reversed[i] = in[$bits(in) - i - 1];
    end

    mode= pe_pkg::PRECISION_CONFIG_8B;

    shift_val[0] = 3;
    shift_val[1] = 0;
    shift_val[2] = 2;
    shift_val[3] = 1;

    #100 $display("%H", out);
    shift_val[3] = 0;

    in_0 = 1;
    in_1 = 1;
    out_full = in_0 * in_1;
    out_half = in_0 * in_1;

    $display(out_full);
    $display(out_half);
    $display("%h", out_posit);
    $finish;
  end

endmodule

