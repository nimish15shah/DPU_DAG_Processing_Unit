//=======================================================================
// Created by         : KU Leuven
// Filename           : streams_top.sv
// Author             : Nimish Shah
// Created On         : 2020-01-08 14:10
// Last Modified      : 
// Update Count       : 2020-01-08 14:10
// Description        : 
//                      
//=======================================================================

`ifndef STREAMS_TOP_DEF
  `define STREAMS_TOP_DEF
  
  `include "common.sv"
  `include "stream.sv"
 
module streams_top (
  input clk,
  input rst,
  
  input [N_PE - 1 : 0] config_stream_instr_slp,
  input [N_PE - 1 : 0] config_stream_ld_slp,
  input [N_PE - 1 : 0] config_stream_st_slp,

  input [N_PE - 1 : 0] config_stream_instr_sd,
  input [N_PE - 1 : 0] config_stream_ld_sd,
  input [N_PE - 1 : 0] config_stream_st_sd,

  // monitor interface
  output [N_PE - 1 : 0] monitor_instr_stream_req,
  output [N_PE - 1 : 0] monitor_instr_stream_gnt,
  output [N_PE - 1 : 0] monitor_ld_stream_req,
  output [N_PE - 1 : 0] monitor_ld_stream_gnt,
  output [N_PE - 1 : 0] monitor_st_stream_req,
  output [N_PE - 1 : 0] monitor_st_stream_gnt,
  
  // io
  input [DATA_L - 1 : 0]                                                   wr_data_io,
  input unsigned [$clog2(N_PE) +stream_pkg::INSTR_STR_ADDR_L + 2 - 1 : 0] full_addr_io,
  input                                                                    wr_vld_io,
  input                                                                    rd_vld_io,

  output [DATA_L - 1 : 0] rd_data_io,
  output                  rd_data_vld_io,

  input                   reset_execution_io,
  input                   enable_execution_io,
  output                  done_execution_io,

  input unsigned [N_PE - 1 : 0][stream_pkg::INSTR_STR_ADDR_L - 1 : 0] instr_stream_start_addr_io,
  input unsigned [N_PE - 1 : 0][stream_pkg::INSTR_STR_ADDR_L - 1 : 0] instr_stream_end_addr_io,

  input unsigned [N_PE - 1 : 0][stream_pkg::LD_STR_ADDR_L - 1 : 0]    ld_stream_start_addr_io,
  input unsigned [N_PE - 1 : 0][stream_pkg::LD_STR_ADDR_L - 1 : 0]    ld_stream_end_addr_io,

  input unsigned [N_PE - 1 : 0][stream_pkg::ST_STR_ADDR_L - 1 : 0]    st_stream_start_addr_io,
  input unsigned [N_PE - 1 : 0][stream_pkg::ST_STR_ADDR_L - 1 : 0]    st_stream_end_addr_io,

  output [N_PE - 1 : 0][stream_pkg::INSTR_STR_WORD_L - 1 : 0] instr,
  output [N_PE - 1 : 0]                                       instr_vld,
  input  [N_PE - 1 : 0]                                       instr_rdy,

  output [N_PE - 1 : 0][stream_pkg::LD_STR_WORD_L - 1 : 0]    ld_addr,
  output [N_PE - 1 : 0]                                       ld_addr_vld,
  input  [N_PE - 1 : 0]                                       ld_addr_rdy,

  output [N_PE - 1 : 0][stream_pkg::ST_STR_WORD_L - 1 : 0]    st_addr,
  output [N_PE - 1 : 0]                                       st_addr_vld,
  input  [N_PE - 1 : 0]                                       st_addr_rdy
); 
  import stream_pkg::*;
  
  localparam STREAM_ID_L= $clog2(N_PE);

  localparam MAX_ADDR_L= INSTR_STR_ADDR_L;
  localparam STREAM_ID_START= MAX_ADDR_L;
  localparam TYPE_START = STREAM_ID_START + STREAM_ID_L;
  
  localparam TYPE_L= 2;
  localparam INSTR_TYPE= 0;
  localparam LD_TYPE= 1;
  localparam ST_TYPE= 2;
  
  logic [TYPE_L - 1 : 0]      type_io;
  logic [STREAM_ID_L - 1 : 0] stream_io;
  logic [MAX_ADDR_L - 1 : 0]  addr_io;

  logic wr_vld_io_instr;
  logic wr_vld_io_ld;
  logic wr_vld_io_st;

  logic rd_vld_io_instr;
  logic rd_vld_io_ld;
  logic rd_vld_io_st;

  logic [INSTR_STR_WORD_L - 1 : 0] rd_data_io_instr;
  logic [LD_STR_WORD_L - 1 : 0] rd_data_io_ld;
  logic [ST_STR_WORD_L - 1 : 0] rd_data_io_st;
  logic [DATA_L - 1 : 0] rd_data_io_pre;

  logic rd_data_vld_io_instr;
  logic rd_data_vld_io_ld;
  logic rd_data_vld_io_st;

  logic done_execution_io_instr;
  logic done_execution_io_ld;
  logic done_execution_io_st;

  logic [N_PE - 1 : 0] instr_vld_pre;
  logic [N_PE - 1 : 0] ld_vld_pre;
  logic [N_PE - 1 : 0] st_vld_pre;

  assign type_io   = full_addr_io[TYPE_START +: TYPE_L];
  assign stream_io = full_addr_io[STREAM_ID_START +: STREAM_ID_L];
  assign addr_io   = full_addr_io[0 +: MAX_ADDR_L];

  always_comb begin
    wr_vld_io_instr = '0;
    wr_vld_io_ld = '0;
    wr_vld_io_st = '0;
    case (type_io) 
      INSTR_TYPE : wr_vld_io_instr = wr_vld_io;
      LD_TYPE    : wr_vld_io_ld    = wr_vld_io;
      ST_TYPE    : wr_vld_io_st    = wr_vld_io;
      default    : ;
    endcase
  end

  always_comb begin
    rd_vld_io_instr = '0;
    rd_vld_io_ld = '0;
    rd_vld_io_st = '0;
    case (type_io) 
      INSTR_TYPE : rd_vld_io_instr = rd_vld_io;
      LD_TYPE    : rd_vld_io_ld    = rd_vld_io;
      ST_TYPE    : rd_vld_io_st    = rd_vld_io;
    endcase
  end


  always_comb begin
    rd_data_io_pre= '0;
    if (rd_data_vld_io_instr) begin
      rd_data_io_pre = rd_data_io_instr;
    end else if (rd_data_vld_io_ld) begin
      rd_data_io_pre = rd_data_io_ld;
    end else if (rd_data_vld_io_st) begin
      rd_data_io_pre = rd_data_io_st;
    end
  end


  multiple_streams #( 
    .N_STREAMS     (N_PE), 
    .STREAM_ADDR_L (INSTR_STR_ADDR_L),
    .STREAM_W      (INSTR_STR_WORD_L),
    .RD_LATENCY    (STR_RD_LATENCY)
  ) 
  MULTIPLE_STREAMS_INSTR_INS
  (
    .clk                  (clk                                     ) ,
    .rst                  (rst                                     ) ,
    
    .slp  (config_stream_instr_slp),
    .sd   (config_stream_instr_sd),

    .wr_data_io           (wr_data_io[0 +: INSTR_STR_WORD_L]       ) ,
    .addr_io           (addr_io                                 ) ,
    .stream_id_io      (stream_io                               ) ,
    .wr_vld_io            (wr_vld_io_instr                         ) ,

    .rd_vld_io       (rd_vld_io_instr                    ) ,

    .rd_data_io           (rd_data_io_instr[0 +: INSTR_STR_WORD_L] ) ,
    .rd_data_vld_io       (rd_data_vld_io_instr                    ) ,

    .reset_execution_io   (reset_execution_io                      ) ,
    .enable_execution_io  (enable_execution_io                     ) ,
    .done_execution_io    (done_execution_io_instr                 ) ,

    .stream_start_addr_io (instr_stream_start_addr_io              ) ,
    .stream_end_addr_io   (instr_stream_end_addr_io                ) ,

    .data_pe              (instr                                   ) ,
    .vld_pe               (instr_vld_pre                               ) ,
    .rdy_pe               (instr_rdy                               )
  ); 
  
  multiple_streams #( 
    .N_STREAMS     (N_PE), 
    .STREAM_ADDR_L (LD_STR_ADDR_L),
    .STREAM_W      (LD_STR_WORD_L),
    .RD_LATENCY    (STR_RD_LATENCY)
  ) 
  MULTIPLE_STREAMS_LD_INS
  (
    .clk                  (clk                                ) ,
    .rst                  (rst                                ) ,

    .slp  (config_stream_ld_slp),
    .sd   (config_stream_ld_sd),

    .wr_data_io           (wr_data_io [0 +: LD_STR_WORD_L]    ) ,
    .addr_io           (addr_io [0 +: LD_STR_ADDR_L]       ) ,
    .stream_id_io      (stream_io                          ) ,
    .wr_vld_io            (wr_vld_io_ld                       ) ,

    .rd_vld_io       (rd_vld_io_ld                  ) ,

    .rd_data_io           (rd_data_io_ld [0 +: LD_STR_WORD_L] ) ,
    .rd_data_vld_io       (rd_data_vld_io_ld                  ) ,

    .reset_execution_io   (reset_execution_io                 ) ,
    .enable_execution_io  (enable_execution_io                ) ,
    .done_execution_io    (done_execution_io_ld               ) ,

    .stream_start_addr_io (ld_stream_start_addr_io            ) ,
    .stream_end_addr_io   (ld_stream_end_addr_io              ) ,

    .data_pe              (ld_addr                            ) ,
    .vld_pe               (ld_vld_pre                        ) ,
    .rdy_pe               (ld_addr_rdy                        )
  ); 

  multiple_streams #( 
    .N_STREAMS     (N_PE), 
    .STREAM_ADDR_L (ST_STR_ADDR_L),
    .STREAM_W      (ST_STR_WORD_L),
    .RD_LATENCY    (STR_RD_LATENCY)
  ) 
  MULTIPLE_STREAMS_ST_INS
  (
    .clk                  (clk                                ),
    .rst                  (rst                                ),

    .slp  (config_stream_st_slp),
    .sd   (config_stream_st_sd),

    .wr_data_io           (wr_data_io [0 +: ST_STR_WORD_L]    ),
    .addr_io           (addr_io [0 +: ST_STR_ADDR_L]       ),
    .stream_id_io      (stream_io                          ),
    .wr_vld_io            (wr_vld_io_st                       ),

    .rd_vld_io       (rd_vld_io_st                  ),

    .rd_data_io           (rd_data_io_st [0 +: ST_STR_WORD_L] ),
    .rd_data_vld_io       (rd_data_vld_io_st                  ),

    .reset_execution_io   (reset_execution_io                 ),
    .enable_execution_io  (enable_execution_io                ),
    .done_execution_io    (done_execution_io_st               ),

    .stream_start_addr_io (st_stream_start_addr_io            ),
    .stream_end_addr_io   (st_stream_end_addr_io              ),

    .data_pe              (st_addr                            ),
    .vld_pe               (st_vld_pre                        ),
    .rdy_pe               (st_addr_rdy)
  ); 
  
  
  assign rd_data_io = rd_data_io_pre;
  assign rd_data_vld_io = (rd_data_vld_io_instr == 0 && rd_data_vld_io_ld == 0 && rd_data_vld_io_st == 0) ? 0 : 1;

  assign done_execution_io = done_execution_io_instr;

  assign monitor_instr_stream_req= instr_vld_pre;
  assign monitor_instr_stream_gnt= instr_rdy;
  assign monitor_ld_stream_req   = ld_vld_pre;
  assign monitor_ld_stream_gnt   = ld_addr_rdy;
  assign monitor_st_stream_req   = st_vld_pre;
  assign monitor_st_stream_gnt   = st_addr_rdy;

  assign instr_vld   = instr_vld_pre;
  assign ld_addr_vld = ld_vld_pre;
  assign st_addr_vld = st_vld_pre;

  initial assert (INSTR_STR_ADDR_L >= LD_STR_ADDR_L) else $warning("size of addr_io etc. is incorrect");
  initial assert (INSTR_STR_ADDR_L >= ST_STR_ADDR_L) else $warning("size of addr_io etc. is incorrect");

endmodule

`endif //STREAMS_TOP_DEF
