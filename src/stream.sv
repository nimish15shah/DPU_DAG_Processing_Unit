//=======================================================================
// Created by         : KU Leuven
// Filename           : stream.sv
// Author             : Nimish Shah
// Created On         : 2020-01-06 11:48
// Last Modified      : 
// Update Count       : 2020-01-06 11:48
// Description        : 
//                      
//=======================================================================


`ifndef STREAM_DEF
  `define STREAM_DEF
  
  `include "common.sv" 
  `include "mem_model.sv"
  `include "flow_control_utils.sv"

module multiple_streams #(parameter N_STREAMS= 8, STREAM_ADDR_L= 10, STREAM_W= 24, RD_LATENCY= 1)(
  input clk,
  input rst,

  input [N_STREAMS - 1 : 0] slp,
  input [N_STREAMS - 1 : 0] sd,

  input [STREAM_W - 1 : 0]                                  wr_data_io,
  input unsigned [STREAM_ADDR_L - 1 : 0]                    addr_io,
  input [$clog2(N_STREAMS) - 1 : 0]                         stream_id_io,
  input                                                     wr_vld_io,
  input                                                     rd_vld_io,

  output [STREAM_W - 1 : 0]                                 rd_data_io,
  output                                                    rd_data_vld_io,

  input                                                     reset_execution_io,
  input                                                     enable_execution_io,
  output                                                    done_execution_io,

  input unsigned [N_STREAMS - 1 : 0][STREAM_ADDR_L - 1 : 0] stream_start_addr_io,
  input unsigned [N_STREAMS - 1 : 0][STREAM_ADDR_L - 1 : 0] stream_end_addr_io,

  output [N_STREAMS - 1 : 0][STREAM_W - 1 : 0]              data_pe,
  output [N_STREAMS - 1 : 0]                                vld_pe,
  input  [N_STREAMS - 1 : 0]                                rdy_pe
); 
  
  logic [N_STREAMS - 1 : 0] wr_vld_per_stream_io;
  logic [N_STREAMS - 1 : 0] rd_addr_vld_per_stream_io;

  logic [N_STREAMS - 1 : 0] [STREAM_W - 1 : 0] rd_data_per_stream_io;
  logic [N_STREAMS - 1 : 0] rd_data_vld_per_stream_io;

  logic [N_STREAMS - 1 : 0] done_execution_per_stream_io;

  localparam DELAY = RD_LATENCY;
  logic [DELAY - 1 : 0] [$clog2(N_STREAMS) - 1 : 0] rd_stream_id_io_delayed;
  

  always_ff @(posedge clk or negedge rst) begin
    if (rst== RESET_STATE) begin
      rd_stream_id_io_delayed <= '0;
    end else begin
      rd_stream_id_io_delayed[0] <= stream_id_io;
      for (integer i=1; i< DELAY ; i=i+1) begin
        rd_stream_id_io_delayed [i] <= rd_stream_id_io_delayed[i-1];
      end
    end
  end
  
  always_comb begin
    wr_vld_per_stream_io = '0;
    rd_addr_vld_per_stream_io= '0;
    wr_vld_per_stream_io[stream_id_io] = wr_vld_io;
    rd_addr_vld_per_stream_io[stream_id_io] = rd_vld_io;
  end

  generate
    genvar stream_i;
    for (stream_i=0; stream_i< N_STREAMS; stream_i=stream_i+1) begin: stream_loop

      stream #(
        .STREAM_ADDR_L(STREAM_ADDR_L), 
        .STREAM_W (STREAM_W), 
        .RD_LATENCY (RD_LATENCY)) 
      STREAM_INS (
        .clk                  (clk                  ),
        .rst                  (rst                  ),

        .slp  (slp [stream_i]),
        .sd   (sd  [stream_i]),
                                                    
        .wr_data_io           (wr_data_io                          ),
        .addr_io              (addr_io                             ),
        .wr_vld_io            (wr_vld_per_stream_io [stream_i]     ),

        .rd_vld_io            (rd_addr_vld_per_stream_io [stream_i]),

        .rd_data_io           (rd_data_per_stream_io [stream_i]    ),
        .rd_data_vld_io       (rd_data_vld_per_stream_io [stream_i]),

        .reset_execution_io   (reset_execution_io                     ),
        .enable_execution_io  (enable_execution_io                    ),
        .done_execution_io    (done_execution_per_stream_io [stream_i]),
                                                    
        .stream_start_addr_io (stream_start_addr_io [stream_i]),
        .stream_end_addr_io   (stream_end_addr_io   [stream_i]),
                                                    
        .data_pe              (data_pe              [stream_i]),
        .vld_pe               (vld_pe               [stream_i]),
        .rdy_pe               (rdy_pe               [stream_i])      
      ); 
    end
  endgenerate

  assign rd_data_io = rd_data_per_stream_io[rd_stream_id_io_delayed[DELAY - 1]];
  assign rd_data_vld_io = rd_data_vld_per_stream_io[rd_stream_id_io_delayed[DELAY - 1]];
  
  assign done_execution_io = (done_execution_per_stream_io == {N_STREAMS{1'b1}}) ? 1'b1 : 1'b0;
endmodule

module stream #(parameter STREAM_ADDR_L= 10, STREAM_W= 24, RD_LATENCY= 1) (
  input clk,
  input rst,

  input slp,
  input sd,

  input [STREAM_W - 1 : 0]               wr_data_io,
  input unsigned [STREAM_ADDR_L - 1 : 0] addr_io,
  input                                  wr_vld_io,
  input                                  rd_vld_io,

  output [STREAM_W - 1 : 0]              rd_data_io,
  output                                 rd_data_vld_io,

  input                                  reset_execution_io,
  input                                  enable_execution_io,
  output                                 done_execution_io,

  input unsigned [STREAM_ADDR_L - 1 : 0] stream_start_addr_io,
  input unsigned [STREAM_ADDR_L - 1 : 0] stream_end_addr_io,
  
  output [STREAM_W - 1 : 0]              data_pe,
  output                                 vld_pe,
  input                                  rdy_pe
  
); 
  

  logic unsigned [STREAM_ADDR_L - 1 : 0] mem_addr;
  logic                                  mem_wr_en;
  logic                                  mem_rd_en;
  logic                                  mem_ch_en;
  logic [STREAM_W - 1 : 0]               mem_wr_data;
  logic [STREAM_W - 1 : 0]               mem_rd_data;
  
  logic ongoing_execution;
  logic done_execution_io_pre;
  logic vld_pe_pre;
  
  logic unsigned [STREAM_ADDR_L - 1 : 0] stream_addr_q;
  logic stream_addr_incr;
  
  logic [RD_LATENCY - 1 : 0] rd_addr_vld_io_delayed;

  logic enable_execution_q;

  assign mem_ch_en = mem_wr_en | mem_rd_en;

  assign mem_wr_en = ongoing_execution ? 0 : wr_vld_io;
  assign mem_wr_data = wr_data_io;

  assign done_execution_io_pre= (stream_addr_q == (stream_end_addr_io + 1)) ? 1'b1 : 1'b0;
  assign ongoing_execution = done_execution_io_pre ? 1'b0 : enable_execution_q;
  

  always_comb begin
    mem_addr = stream_addr_q;
    mem_rd_en = 0;
    if (ongoing_execution) begin
      mem_addr = stream_addr_q;
      mem_rd_en = stream_addr_incr;
    end else if (mem_wr_en) begin
      mem_addr = addr_io;
    end else if (rd_vld_io) begin
      mem_addr = addr_io;
      mem_rd_en= 1;
    end
  end

  always_ff @(posedge clk or negedge rst) begin
    if (rst== RESET_STATE) begin
      stream_addr_q <= '0;
    end else begin
      if (reset_execution_io) begin
        stream_addr_q <= stream_start_addr_io;
      end else if (stream_addr_incr) begin
        stream_addr_q <= stream_addr_q + 1;
      end
    end
  end

  always_ff @(posedge clk or negedge rst) begin
    if (rst== RESET_STATE) begin
      rd_addr_vld_io_delayed <= '0;
    end else begin
      rd_addr_vld_io_delayed[0] <= rd_vld_io;
      for (integer i=1; i< RD_LATENCY ; i=i+1) begin
        rd_addr_vld_io_delayed [i] <= rd_addr_vld_io_delayed[i-1];
      end
    end
  end

  always_ff @(posedge clk or negedge rst) begin
    if (rst== RESET_STATE) begin
      enable_execution_q <= '0;
    end else begin
      enable_execution_q <= enable_execution_io;
    end
  end

  sp_mem_model #(
    .DATA_L (STREAM_W),
    .ADDR_L (STREAM_ADDR_L),
    .RD_LATENCY (RD_LATENCY)
  ) SP_MEM_MODEL_INS
  (
    .clk     (clk     ),
    .rst     (rst     ),
                      
    .slp     (slp),
    .sd      (sd),

    .wr_en   (mem_wr_en   ),
    .ch_en   (mem_ch_en   ),
    .addr    (mem_addr    ),
    .wr_data (mem_wr_data ),
    .rd_data (mem_rd_data )
  ); 
  
  flow_control_vld_rdy_with_latency #(.LATENCY(RD_LATENCY)) FLOW_CONTROL_VLD_RDY_WITH_LATENCY_INS (
    .clk          (clk),
    .rst          (rst),

    .en           (ongoing_execution),
    .flush        (1'b0),
    .reset_state  (reset_execution_io),
    .rdy          (rdy_pe),

    .do_operation (stream_addr_incr),
    .vld          (vld_pe_pre)
  );

  assign rd_data_io = mem_rd_data;
  assign rd_data_vld_io = rd_addr_vld_io_delayed[RD_LATENCY - 1];
  
  assign data_pe = enable_execution_q ? mem_rd_data : 0;
  assign vld_pe = vld_pe_pre;

  assign done_execution_io= done_execution_io_pre;

  assert property (@(posedge clk) if (wr_vld_io) (!rd_vld_io)) else $warning("RD and Wr cannot be simultaneous");
  assert property (@(posedge clk) if (ongoing_execution) (!wr_vld_io)) else $warning("IO should not interfere execution");
  assert property (@(posedge clk) if (ongoing_execution) (!rd_vld_io)) else $warning(1);

  assert property (@(posedge clk) if (ongoing_execution) (stream_start_addr_io <= stream_end_addr_io)) else $warning(1);
endmodule

`endif //STREAM_DEF
