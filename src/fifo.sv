`ifndef FIFO_DEF
  `define FIFO_DEF

`include "common.sv"

module fifo #(parameter WORD_L= 8, DEPTH= 8, PORT_L= 8) (
    input  logic                                  clk,
    input  logic                                  rst,

    input  logic [0 : PORT_L - 1 ][WORD_L -1 : 0] inputs,
    input  logic                                  in_vld,
    output logic                                  fifo_rdy,

    output logic [0 : PORT_L - 1][WORD_L -1 : 0]  outputs,
    output logic                                  fifo_out_vld,
    input  logic                                  receiver_rdy
  ); 
  
  localparam ADR_L = $clog2(DEPTH);
  logic [DEPTH - 1 : 0] [0 : PORT_L - 1] [WORD_L - 1 : 0] fifo_reg;
  logic [ADR_L : 0]                                       wr_adr;
  logic [ADR_L : 0]                                       rd_adr;
  logic                                                   full;
  logic                                                   empty;
  logic                                                   wr_en;
  logic                                                   rd_en;
  logic fifo_rdy_pre;
  logic fifo_out_vld_pre;

  //-------------------------------------------
  //       Flow control
  //-------------------------------------------
  always_comb begin
    if ((wr_adr [ADR_L - 1 : 0] == rd_adr[ADR_L - 1 : 0]) && (wr_adr[ADR_L] != rd_adr[ADR_L])) begin
      full = 1;
    end else begin
      full = 0;
    end
    if (wr_adr == rd_adr) begin
      empty = 1;
    end else begin
      empty = 0;
    end
  end

  assign fifo_rdy_pre = ~full;
  assign fifo_out_vld_pre = ~empty;
  assign wr_en    = fifo_rdy_pre & in_vld;
  assign rd_en    = fifo_out_vld_pre & receiver_rdy;

  //-------------------------------------------
  //       Address generation
  //-------------------------------------------
  always_ff @(posedge clk or negedge rst) begin
    if (rst== RESET_STATE) begin
      wr_adr <= '0;
      rd_adr <= '0;
    end else begin
      if (wr_en) begin
        wr_adr <= wr_adr + 1;
      end
      if (rd_en) begin
        rd_adr <= rd_adr + 1;
      end
    end
  end

  //-------------------------------------------
  //       FIFO registers
  //-------------------------------------------
  always_ff @(posedge clk or negedge rst) begin
    if (rst== RESET_STATE) begin
      fifo_reg <= '0;
    end else begin
      if (wr_en) begin
        fifo_reg[wr_adr[ADR_L-1 : 0]] <= inputs;
      end
    end
  end

  assign outputs = fifo_reg[rd_adr[ADR_L-1 : 0]];
  assign fifo_rdy= fifo_rdy_pre;
  assign fifo_out_vld= fifo_out_vld_pre;
  //===========================================
  //       Assertions
  //===========================================
  initial assert (DEPTH == 2**ADR_L) else $warning("DEPTH should be a power of 2");
    
  assert property (@(posedge clk) if (!fifo_rdy) (fifo_out_vld)) else $warning("Cannot be full and empty at the same time");

  assert property (@(posedge clk) if (in_vld) (!$isunknown(inputs))) else $warning(1);
  assert property (@(posedge clk) if (fifo_out_vld) (!$isunknown(outputs))) else $warning(1);

endmodule

module fifo_2out #(parameter WORD_L= 8, DEPTH= 8, PORT_L= 8) (
  input  logic                                  clk,
  input  logic                                  rst,

  input  logic [0 : PORT_L - 1 ][WORD_L -1 : 0] inputs,
  input  logic                                  in_vld,
  output logic                                  fifo_rdy,

  output logic [0 : PORT_L - 1][WORD_L -1 : 0]  outputs_0,
  output logic [0 : PORT_L - 1][WORD_L -1 : 0]  outputs_1,
  output logic                                  fifo_out_0_vld,
  output logic                                  fifo_out_1_vld,
  input  logic                                  receiver_0_rdy,
  input  logic                                  receiver_1_rdy
); 
  localparam ADR_L = $clog2(DEPTH);
  logic [DEPTH - 1 : 0] [0 : PORT_L - 1] [WORD_L - 1 : 0] fifo_reg;
  logic [ADR_L : 0]                                       wr_adr;
  logic [ADR_L : 0]                                       rd_adr_0;
  logic [ADR_L : 0]                                       rd_adr_1;
  logic                                                   full;
  logic                                                   empty;
  logic                                                   wr_en;
  logic                                                   rd_en_0;
  logic                                                   rd_en_1;
  logic fifo_rdy_pre;
  logic fifo_out_0_vld_pre;
  logic fifo_out_1_vld_pre;
  
  assign rd_adr_1 = rd_adr_0 + 1;
  //-------------------------------------------
  //       Flow control
  //-------------------------------------------
  always_comb begin
    if ((wr_adr [ADR_L - 1 : 0] == rd_adr_0[ADR_L - 1 : 0]) && (wr_adr[ADR_L] != rd_adr_0[ADR_L])) begin
      full = 1;
    end else begin
      full = 0;
    end
    if (wr_adr == rd_adr_0) begin
      empty = 1;
    end else begin
      empty = 0;
    end
  end

  assign fifo_rdy_pre = ~full;
  
  // If receiver requests 2 packets, only assert 1st valid if 2nd valid is also high
  //assign fifo_out_0_vld_pre = receiver_1_rdy ? fifo_out_1_vld_pre : ~empty; 
  assign fifo_out_0_vld_pre = ~empty; 
  assign fifo_out_1_vld_pre = empty ? 0 : ((wr_adr == rd_adr_1) ? 0 : 1);

  assign wr_en    = fifo_rdy_pre & in_vld;
  assign rd_en_0    = fifo_out_0_vld_pre & receiver_0_rdy;
  assign rd_en_1    = fifo_out_1_vld_pre & receiver_1_rdy;


  //-------------------------------------------
  //       Address generation
  //-------------------------------------------

  always_ff @(posedge clk or negedge rst) begin
    if (rst== RESET_STATE) begin
      wr_adr <= '0;
      rd_adr_0 <= '0;
    end else begin
      if (wr_en) begin
        wr_adr <= wr_adr + 1;
      end
      if (rd_en_1 && rd_en_0) begin
        rd_adr_0 <= rd_adr_0 + 2;
      end else if (~rd_en_1 && rd_en_0) begin
        rd_adr_0 <= rd_adr_0 + 1;
      end else if (rd_en_1 && ~rd_en_0) begin
        $warning(1);
      end
    end
  end

  //-------------------------------------------
  //       FIFO registers
  //-------------------------------------------
  always_ff @(posedge clk or negedge rst) begin
    if (rst== RESET_STATE) begin
      fifo_reg <= '0;
    end else begin
      if (wr_en) begin
        fifo_reg[wr_adr[ADR_L-1 : 0]] <= inputs;
      end
    end
  end


  assign outputs_0 = fifo_reg[rd_adr_0[ADR_L-1 : 0]];
  assign outputs_1 = fifo_reg[rd_adr_1[ADR_L-1 : 0]];
  assign fifo_rdy = fifo_rdy_pre;
  assign fifo_out_0_vld = fifo_out_0_vld_pre;
  assign fifo_out_1_vld = fifo_out_1_vld_pre;

  //===========================================
  //       Assertions
  //===========================================
  initial assert (DEPTH == 2**ADR_L) else $warning("DEPTH should be a power of 2");
  assert property (@(posedge clk) if (!receiver_0_rdy) (!receiver_1_rdy)) else $warning("receiver_1_rdy cannot be high without receiver_0_rdy");
  assert property (@(posedge clk) if (!fifo_rdy) (fifo_out_0_vld)) else $warning("Cannot be full and empty at the same time");
  assert property (@(posedge clk) if (!fifo_rdy) (fifo_out_1_vld)) else $warning(1);

 
  assert property (@(posedge clk) if (in_vld) (!$isunknown(inputs))) else $warning(1);
  assert property (@(posedge clk) if (fifo_out_0_vld) (!$isunknown(outputs_0))) else $warning(1);
  assert property (@(posedge clk) if (fifo_out_1_vld) (!$isunknown(outputs_1))) else $warning(1);
endmodule


`endif //FIFO_DEF
