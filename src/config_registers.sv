//=======================================================================
// Created by         : KU Leuven
// Filename           : config_registers.sv
// Author             : Nimish Shah
// Created On         : 2020-01-08 16:26
// Last Modified      : 
// Update Count       : 2020-01-08 16:26
// Description        : 
//                      
//=======================================================================

`ifndef CONFIG_REGISTERS_DEF
  `define CONFIG_REGISTERS_DEF

  `include "common.sv"
// Declare all paths from config regs to actual usage as false paths if not
// meeting timing
module config_registers #(parameter CONFIG_L = 32) (
  input clk,
  input rst,

  output unsigned [N_PE - 1 : 0][stream_pkg::INSTR_STR_ADDR_L - 1 : 0] instr_stream_start_addr_io,
  output unsigned [N_PE - 1 : 0][stream_pkg::INSTR_STR_ADDR_L - 1 : 0] instr_stream_end_addr_io,

  output unsigned [N_PE - 1 : 0][stream_pkg::LD_STR_ADDR_L - 1 : 0]    ld_stream_start_addr_io,
  output unsigned [N_PE - 1 : 0][stream_pkg::LD_STR_ADDR_L - 1 : 0]    ld_stream_end_addr_io,

  output unsigned [N_PE - 1 : 0][stream_pkg::ST_STR_ADDR_L - 1 : 0]    st_stream_start_addr_io,
  output unsigned [N_PE - 1 : 0][stream_pkg::ST_STR_ADDR_L - 1 : 0]    st_stream_end_addr_io,

  output [PRECISION_CONFIG_L - 1 : 0] precision_config,

  output [N_PE - 1 : 0] config_local_mem_slp,
  output [N_PE - 1 : 0] config_local_mem_sd,

  output [N_PE - 1 : 0] config_global_mem_slp,
  output [N_PE - 1 : 0] config_global_mem_sd,
  
  output [N_PE - 1 : 0] config_stream_instr_slp,
  output [N_PE - 1 : 0] config_stream_ld_slp,
  output [N_PE - 1 : 0] config_stream_st_slp,

  output [N_PE - 1 : 0] config_stream_instr_sd,
  output [N_PE - 1 : 0] config_stream_ld_sd,
  output [N_PE - 1 : 0] config_stream_st_sd,

  input [CONFIG_L - 1 : 0] data_in,
  output [CONFIG_L - 1 : 0] data_out,

  input shift_en
); 

  localparam N_REG = (N_PE * 6) + 1 + ((N_PE/CONFIG_L) * 10);
  localparam PRECISION_CONFIG_REG_I= N_PE * 6;

  logic [N_REG - 1 : 0] [CONFIG_L - 1 : 0] shift_reg;

  always_ff @(posedge clk or negedge rst) begin
    if (rst== RESET_STATE) begin
      shift_reg <= '0;
    end else begin
      if (shift_en) begin
        shift_reg[0] <= data_in;
        for (integer i=1; i< N_REG ; i=i+1) begin
          shift_reg[i] <= shift_reg[i-1];
        end
      end
    end
  end
  
  generate
    genvar i;
    for (i=0; i< N_PE ; i=i+1) begin: config_loog
      assign instr_stream_start_addr_io [i] =  shift_reg[i * 6 + 0];
      assign instr_stream_end_addr_io   [i] =  shift_reg[i * 6 + 1];

      assign ld_stream_start_addr_io    [i] =  shift_reg[i * 6 + 2];
      assign ld_stream_end_addr_io      [i] =  shift_reg[i * 6 + 3];

      assign st_stream_start_addr_io    [i] =  shift_reg[i * 6 + 4];
      assign st_stream_end_addr_io      [i] =  shift_reg[i * 6 + 5];

    end
  endgenerate
  
  assign precision_config = shift_reg[PRECISION_CONFIG_REG_I];

`ifdef DESIGN_EXPLORE
  assign config_local_mem_slp   = 0; 
  assign config_local_mem_slp   = 0; 
  assign config_local_mem_sd    = 0; 
  assign config_local_mem_sd    = 0; 
                            
  assign config_global_mem_slp  = 0; 
  assign config_global_mem_slp  = 0; 
  assign config_global_mem_sd   = 0; 
  assign config_global_mem_sd   = 0; 
                               
  assign config_stream_instr_slp = 0;
  assign config_stream_instr_slp = 0;
  assign config_stream_ld_slp   = 0; 
  assign config_stream_ld_slp   = 0; 
  assign config_stream_st_slp   = 0; 
  assign config_stream_st_slp   = 0; 
                              
  assign config_stream_instr_sd = 0; 
  assign config_stream_instr_sd = 0; 
  assign config_stream_ld_sd    = 0; 
  assign config_stream_ld_sd    = 0; 
  assign config_stream_st_sd    = 0; 
  assign config_stream_st_sd    = 0; 
`else
  assign config_local_mem_slp   [0       +: CONFIG_L] = shift_reg[PRECISION_CONFIG_REG_I+1];
  assign config_local_mem_slp   [CONFIG_L+: CONFIG_L] = shift_reg[PRECISION_CONFIG_REG_I+2];
  assign config_local_mem_sd    [0       +: CONFIG_L] = shift_reg[PRECISION_CONFIG_REG_I+3];
  assign config_local_mem_sd    [CONFIG_L+: CONFIG_L] = shift_reg[PRECISION_CONFIG_REG_I+4];

  assign config_global_mem_slp  [0       +: CONFIG_L] = shift_reg[PRECISION_CONFIG_REG_I+5];
  assign config_global_mem_slp  [CONFIG_L+: CONFIG_L] = shift_reg[PRECISION_CONFIG_REG_I+6];
  assign config_global_mem_sd   [0       +: CONFIG_L] = shift_reg[PRECISION_CONFIG_REG_I+7];
  assign config_global_mem_sd   [CONFIG_L+: CONFIG_L] = shift_reg[PRECISION_CONFIG_REG_I+8];

  assign config_stream_instr_slp[0       +: CONFIG_L] = shift_reg[PRECISION_CONFIG_REG_I+9];
  assign config_stream_instr_slp[CONFIG_L+: CONFIG_L] = shift_reg[PRECISION_CONFIG_REG_I+10];
  assign config_stream_ld_slp   [0       +: CONFIG_L] = shift_reg[PRECISION_CONFIG_REG_I+11];
  assign config_stream_ld_slp   [CONFIG_L+: CONFIG_L] = shift_reg[PRECISION_CONFIG_REG_I+12];
  assign config_stream_st_slp   [0       +: CONFIG_L] = shift_reg[PRECISION_CONFIG_REG_I+13];
  assign config_stream_st_slp   [CONFIG_L+: CONFIG_L] = shift_reg[PRECISION_CONFIG_REG_I+14];

  assign config_stream_instr_sd [0       +: CONFIG_L] = shift_reg[PRECISION_CONFIG_REG_I+15];
  assign config_stream_instr_sd [CONFIG_L+: CONFIG_L] = shift_reg[PRECISION_CONFIG_REG_I+16];
  assign config_stream_ld_sd    [0       +: CONFIG_L] = shift_reg[PRECISION_CONFIG_REG_I+17];
  assign config_stream_ld_sd    [CONFIG_L+: CONFIG_L] = shift_reg[PRECISION_CONFIG_REG_I+18];
  assign config_stream_st_sd    [0       +: CONFIG_L] = shift_reg[PRECISION_CONFIG_REG_I+19];
  assign config_stream_st_sd    [CONFIG_L+: CONFIG_L] = shift_reg[PRECISION_CONFIG_REG_I+20];
`endif

  assign data_out = shift_reg[N_REG - 1];
endmodule


`endif //CONFIG_REGISTERS_DEF
