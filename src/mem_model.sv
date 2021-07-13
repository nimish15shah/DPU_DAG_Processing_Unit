//=======================================================================
// Created by         : KU Leuven
// Filename           : mem_model.sv
// Author             : Nimish Shah
// Created On         : 2019-12-18 21:33
// Last Modified      : 
// Update Count       : 2019-12-18 21:33
// Description        : 
//                      
//=======================================================================

`ifndef MEM_MODEL_DEF
  `define MEM_MODEL_DEF

`ifdef USE_SRAM_MACRO
module sp_mem_model #(
  parameter DATA_L= 8,
  parameter ADDR_L= 8,
  parameter RD_LATENCY
)
(
  input clk,
  input rst,
  
  input slp,
  input sd,
  
  input wr_en, // active high
  input ch_en, // active high
  input [ADDR_L - 1 : 0] addr,
  input [DATA_L - 1 : 0] wr_data,
  output [DATA_L - 1 : 0] rd_data
); 
  
  logic [31 : 0] wr_data_resized_32;
  logic [23 : 0] wr_data_resized_24;
  logic [31 : 0] rd_data_resized_32;
  logic [23 : 0] rd_data_resized_24;
  logic [DATA_L - 1 : 0] rd_data_pre;

  assign wr_data_resized_32 = wr_data;
  assign wr_data_resized_24 = wr_data;


  generate
    if (DATA_L >24 && DATA_L <= 32 && ADDR_L == 10) begin: mem_1024x32
      assign rd_data_pre = rd_data_resized_32;
      TS1N28HPCPHVTB1024X32M4SWBASO SRAM_1024x32 (
        .SLP   (slp),
        .SD    (sd),
        .CLK   (clk),
        .CEB   (~ch_en), // active low
        .WEB   (~wr_en), //active low
        .CEBM  (1'b1),
        .WEBM  (1'b1),
        .AWT   (1'b0),
        .A     (addr),
        .D     (wr_data_resized_32),
        .BWEB  ('0),
        .AM    ('0),
        .DM    ('0),
        .BWEBM ({32{1'b1}}),
        .BIST  (1'b0),
        .Q     (rd_data_resized_32)
      );
    end else if (DATA_L <= 24 && ADDR_L == 10) begin: mem_1024x24
      assign rd_data_pre = rd_data_resized_24;
      TS1N28HPCPHVTB1024X24M4SWBASO SRAM_1024x24 (
        .SLP   (slp),
        .SD    (sd),
        .CLK   (clk),
        .CEB   (~ch_en), // active low
        .WEB   (~wr_en), //active low
        .CEBM  (1'b1),
        .WEBM  (1'b1),
        .AWT   (1'b0),
        .A     (addr),
        .D     (wr_data_resized_24),
        .BWEB  ('0),
        .AM    ('0),
        .DM    ('0),
        .BWEBM ({24{1'b1}}),
        .BIST  (1'b0),
        .Q     (rd_data_resized_24)
      );
    end else if (DATA_L <= 24 && ADDR_L == 9) begin: mem_512x24
      assign rd_data_pre = rd_data_resized_24;
      TS1N28HPCPHVTB512X24M4SWBASO SRAM_512x24 (
        .SLP   (slp),
        .SD    (sd),
        .CLK   (clk),
        .CEB   (~ch_en), // active low
        .WEB   (~wr_en), //active low
        .CEBM  (1'b1),
        .WEBM  (1'b1),
        .AWT   (1'b0),
        .A     (addr),
        .D     (wr_data_resized_24),
        .BWEB  ('0),
        .AM    ('0),
        .DM    ('0),
        .BWEBM ({24{1'b1}}),
        .BIST  (1'b0),
        .Q     (rd_data_resized_24)
      );
    end else if (DATA_L > 24 && DATA_L <= 32 && ADDR_L == 9) begin: mem_512x32
      assign rd_data_pre = rd_data_resized_32;
      TS1N28HPCPHVTB512X32M4SWBASO SRAM_512x32 (
        .SLP   (slp),
        .SD    (sd),
        .CLK   (clk),
        .CEB   (~ch_en), // active low
        .WEB   (~wr_en), //active low
        .CEBM  (1'b1),
        .WEBM  (1'b1),
        .AWT   (1'b0),
        .A     (addr),
        .D     (wr_data_resized_32),
        .BWEB  ('0),
        .AM    ('0),
        .DM    ('0),
        .BWEBM ({32{1'b1}}),
        .BIST  (1'b0),
        .Q     (rd_data_resized_32)
      );
    end
  endgenerate
  
  assign rd_data = rd_data_pre;

  initial begin
    //assert (DATA_L == 32 || DATA_L == 24);
    assert (ADDR_L == 10 || ADDR_L == 9 ); //|| ADDR_L == 8);
  end

  assert property (@(posedge clk) if (wr_en) (!$isunknown(wr_data))) else $warning("%h", wr_data);
  assert property (@(posedge clk) if (ch_en) (!$isunknown(addr))) else $warning("%h", addr);

  assert property (@(posedge clk) (ch_en && ~wr_en) |=> (!$isunknown(rd_data_pre))) else $warning("rd_data_pre cannot be unknow after a read request: %h", rd_data_pre);
endmodule

`else // do not use USE_SRAM_MACRO
  //===========================================
  //       Functional model for memory
  //===========================================
module sp_mem_model #(
  parameter DATA_L= 8,
  parameter ADDR_L= 8,
  parameter RD_LATENCY
)
(
  input clk,
  input rst,

  input slp,
  input sd,
  
  input wr_en,
  input ch_en,
  input [ADDR_L - 1 : 0] addr,
  input [DATA_L - 1 : 0] wr_data,
  output [DATA_L - 1 : 0] rd_data
); 
  
  logic [2**ADDR_L - 1 : 0] [DATA_L - 1 : 0] data_array;
  logic [DATA_L - 1 : 0] rd_data_based_on_en;
  logic [RD_LATENCY - 1 : 0] [DATA_L - 1 : 0] rd_data_delayed;

  always_ff @(posedge clk or negedge rst) begin
    if (rst== RESET_STATE) begin
      data_array <= 'x;
    end else begin
      if (wr_en) begin
        data_array[addr] <= wr_data;
      end
    end
  end

  always_ff @(posedge clk or negedge rst) begin
    if (rst== RESET_STATE) begin
      rd_data_delayed <= 'x;
    end else begin
      if (ch_en) begin
        rd_data_delayed[0]<= rd_data_based_on_en;
        for (integer i=1; i< RD_LATENCY; i=i+1) begin
          rd_data_delayed[i] <= rd_data_delayed[i-1];
        end
      end
    end
  end
  
  assign rd_data_based_on_en= wr_en ? 'x : data_array[addr];

  assign rd_data = rd_data_delayed[RD_LATENCY - 1];


endmodule
`endif


`endif //MEM_MODEL_DEF
