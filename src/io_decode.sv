//=======================================================================
// Created by         : KU Leuven
// Filename           : ../src/io_decode.sv
// Author             : Nimish Shah
// Created On         : 2020-02-25 20:25
// Last Modified      : 
// Update Count       : 2020-02-25 20:25
// Description        : 
//                      
//=======================================================================

`ifndef IO_DECODE_DEF
  `define IO_DECODE_DEF
  
  `include "common.sv"
module io_decode (
  input [periphery_pkg::IO_OPCODE_L - 1 :0] io_opcode,
  output config_shift_en,
  output rd_en, 
  output wr_en,
  output monitor,
  output reg_shift_en
); 
  import periphery_pkg::*;

  logic config_shift_en_pre;
  logic rd_en_pre; 
  logic wr_en_pre;
  logic monitor_pre;
  logic reg_shift_en_pre;

  always_comb begin
    case (io_opcode) 
      IO_OPCODE_NOP : begin 
        config_shift_en_pre = 0;
        rd_en_pre           = 0;
        wr_en_pre           = 0;
        monitor_pre         = 0;
        reg_shift_en_pre     = 0;
      end

      IO_OPCODE_RD_EN : begin 
        config_shift_en_pre = 0;
        rd_en_pre           = 1;
        wr_en_pre           = 0;
        monitor_pre         = 0;
        reg_shift_en_pre    = 0;
      end

      IO_OPCODE_WR_EN : begin 
        config_shift_en_pre = 0;
        rd_en_pre           = 0;
        wr_en_pre           = 1;
        monitor_pre         = 0;
        reg_shift_en_pre    = 0;
      end

      IO_OPCODE_CONFIG_SHIFT_EN : begin 
        config_shift_en_pre = 1;
        rd_en_pre           = 0;
        wr_en_pre           = 0;
        monitor_pre         = 0;
        reg_shift_en_pre    = 0;
      end

      IO_OPCODE_MONITOR : begin 
        config_shift_en_pre = 0;
        rd_en_pre           = 0;
        wr_en_pre           = 0;
        monitor_pre         = 1;
        reg_shift_en_pre    = 0;
      end

      IO_OPCODE_REG_SHIFT_EN : begin 
        config_shift_en_pre = 0;
        rd_en_pre           = 0;
        wr_en_pre           = 0;
        monitor_pre         = 0;
        reg_shift_en_pre    = 1;
      end

      default : begin 
        config_shift_en_pre = 0;
        rd_en_pre           = 0;
        wr_en_pre           = 0;
        monitor_pre         = 0;
        reg_shift_en_pre    = 0;
      end
    endcase
  end

  assign config_shift_en = config_shift_en_pre;
  assign rd_en = rd_en_pre; 
  assign wr_en = wr_en_pre;
  assign monitor = monitor_pre;
  assign reg_shift_en =reg_shift_en_pre;

endmodule


`endif //IO_DECODE_DEF
