//=======================================================================
// Created by         : KU Leuven
// Filename           : pru_async_top.sv
// Author             : Nimish Shah
// Created On         : 2020-01-08 16:57
// Last Modified      : 
// Update Count       : 2020-01-08 16:57
// Description        : 
//                      
//=======================================================================

`ifndef PRU_ASYNC_WO_IO_DEF
  `define PRU_ASYNC_WO_IO_DEF
  
  `include "common.sv"
  `include "config_registers.sv"
  `include "io_access.sv"
  `include "io_registers.sv"
  `include "io_monitor.sv"
  `include "io_decode.sv"
  `include "full_design_wo_periphery.sv"

module pru_async_wo_io (
  input clk,
  input rst,

  input [periphery_pkg::INPUT_DATA_L - 1 : 0] in,

  input [periphery_pkg::IO_OPCODE_L -1 : 0] io_opcode,
  
  input reset_execution_io,
  input enable_execution_io,
  output done_execution_io,

  output [31 : 0] out
); 
  
  localparam IO_OUT_L= periphery_pkg::OUTPUT_DATA_L;


  logic config_shift_en;
  logic rd_en; 
  logic wr_en;
  logic monitor;
  logic reg_shift_en;

  logic [periphery_pkg::INPUT_REG_L - 1 : 0] reg_data;

  logic [N_PE - 1 : 0] monitor_global_rd_req;
  logic [N_PE - 1 : 0] monitor_global_rd_gnt;
  logic [N_PE - 1 : 0] monitor_global_wr_req;
  logic [N_PE - 1 : 0] monitor_global_wr_gnt;

  logic [N_PE - 1 : 0] monitor_instr_stream_req;
  logic [N_PE - 1 : 0] monitor_instr_stream_gnt;
  logic [N_PE - 1 : 0] monitor_ld_stream_req;
  logic [N_PE - 1 : 0] monitor_ld_stream_gnt;
  logic [N_PE - 1 : 0] monitor_st_stream_req;
  logic [N_PE - 1 : 0] monitor_st_stream_gnt;

  logic [N_PE - 1 : 0] [DATA_L - 1 : 0] monitor_pe_out;
  logic [N_PE - 1 : 0] [INSTR_L - 1 : 0] monitor_instr;

  logic [GLOBAL_MEM_ADDR_L - 1 : 0]    init_global_mem_addr;
  logic                                init_global_mem_vld;
  logic                                init_global_mem_wr_en;
  logic [DATA_L - 1 : 0]               init_global_mem_wr_data;
  logic [DATA_L - 1 : 0]               init_global_mem_rd_data;
  logic                                init_global_mem_rd_data_vld;

  logic [LOCAL_MEM_ADDR_L - 1 : 0]      init_local_mem_addr;
  logic [N_PE - 1 : 0]                  init_local_mem_vld;
  logic [N_PE - 1 : 0]                  init_local_mem_wr_en;
  logic [DATA_L - 1 : 0]                init_local_mem_wr_data;
  logic [N_PE - 1 : 0] [DATA_L - 1 : 0] init_local_mem_rd_data;
  logic [N_PE - 1 : 0]                  init_local_mem_rd_data_vld;

  logic [DATA_L - 1 : 0]                                         init_stream_wr_data;
  logic [$clog2(N_PE) +stream_pkg::INSTR_STR_ADDR_L + 2 - 1 : 0] init_stream_addr;
  logic                                                          init_stream_wr_vld;
  logic                                                          init_stream_rd_vld;
  logic [DATA_L - 1 : 0]                                         init_stream_rd_data;
  logic                                                          init_stream_rd_data_vld;

  // config
  logic [N_PE - 1 : 0][stream_pkg::INSTR_STR_ADDR_L - 1 : 0] config_instr_stream_start_addr_io;
  logic [N_PE - 1 : 0][stream_pkg::INSTR_STR_ADDR_L - 1 : 0] config_instr_stream_end_addr_io;

  logic [N_PE - 1 : 0][stream_pkg::LD_STR_ADDR_L - 1 : 0]    config_ld_stream_start_addr_io;
  logic [N_PE - 1 : 0][stream_pkg::LD_STR_ADDR_L - 1 : 0]    config_ld_stream_end_addr_io;

  logic [N_PE - 1 : 0][stream_pkg::ST_STR_ADDR_L - 1 : 0]    config_st_stream_start_addr_io;
  logic [N_PE - 1 : 0][stream_pkg::ST_STR_ADDR_L - 1 : 0]    config_st_stream_end_addr_io;

  logic [PRECISION_CONFIG_L - 1 : 0] config_precision_config;

  logic [N_PE - 1 : 0] config_local_mem_slp;
  logic [N_PE - 1 : 0] config_local_mem_sd;

  logic [N_PE - 1 : 0] config_global_mem_slp;
  logic [N_PE - 1 : 0] config_global_mem_sd;
  
  logic [N_PE - 1 : 0] config_stream_instr_slp;
  logic [N_PE - 1 : 0] config_stream_ld_slp;
  logic [N_PE - 1 : 0] config_stream_st_slp;

  logic [N_PE - 1 : 0] config_stream_instr_sd;
  logic [N_PE - 1 : 0] config_stream_ld_sd;
  logic [N_PE - 1 : 0] config_stream_st_sd;


  // io
  logic [IO_OUT_L - 1 : 0] out_pre;
  logic [IO_OUT_L - 1 : 0] out_init;
  logic [IO_OUT_L - 1 : 0] out_config;
  logic [IO_OUT_L - 1 : 0] out_monitor;

  io_decode IO_DECODE_INS (
    .io_opcode       (io_opcode      ),
    .config_shift_en (config_shift_en),
    .rd_en           (rd_en          ),
    .wr_en           (wr_en          ),
    .monitor         (monitor        ),
    .reg_shift_en    (reg_shift_en   )
  );

  io_registers IO_REGISTERS_INS (
    .clk     (clk     ),
    .rst     (rst     ),

    .in      (in      ),
    .shift_en(reg_shift_en),

    .reg_data(reg_data)
  ); 

  io_mem_access IO_MEM_ACCESS_INS (
    .clk                         (clk),
    .rst                         (rst                         ),
                                                              
    .in                          (reg_data                    ),
                                                              
    .wr_en                       (wr_en                       ),
    .rd_en                       (rd_en                       ),
                                                              
    .init_global_mem_addr        (init_global_mem_addr        ),
    .init_global_mem_vld         (init_global_mem_vld         ),
    .init_global_mem_wr_en       (init_global_mem_wr_en       ),
    .init_global_mem_wr_data     (init_global_mem_wr_data     ),
    .init_global_mem_rd_data     (init_global_mem_rd_data     ),
    .init_global_mem_rd_data_vld (init_global_mem_rd_data_vld ),
                                                              
    .init_local_mem_addr         (init_local_mem_addr         ),
    .init_local_mem_vld          (init_local_mem_vld          ),
    .init_local_mem_wr_en        (init_local_mem_wr_en        ),
    .init_local_mem_wr_data      (init_local_mem_wr_data      ),
    .init_local_mem_rd_data      (init_local_mem_rd_data      ),
    .init_local_mem_rd_data_vld  (init_local_mem_rd_data_vld  ),

    .init_stream_wr_data     (init_stream_wr_data    ),
    .init_stream_addr        (init_stream_addr       ),
    .init_stream_wr_vld      (init_stream_wr_vld     ),
    .init_stream_rd_vld      (init_stream_rd_vld     ),
    .init_stream_rd_data     (init_stream_rd_data    ),
    .init_stream_rd_data_vld (init_stream_rd_data_vld),

    .out  (out_init)
  ); 

  
  config_registers #(.CONFIG_L(IO_OUT_L)) CONFIG_REGISTERS_INS (
    .clk                       (clk),
    .rst                       (rst),

    .instr_stream_start_addr_io(config_instr_stream_start_addr_io),
    .instr_stream_end_addr_io  (config_instr_stream_end_addr_io  ),
                                
    .ld_stream_start_addr_io   (config_ld_stream_start_addr_io   ),
    .ld_stream_end_addr_io     (config_ld_stream_end_addr_io     ),
                               
    .st_stream_start_addr_io   (config_st_stream_start_addr_io   ),
    .st_stream_end_addr_io     (config_st_stream_end_addr_io     ),
                               
    .precision_config          (config_precision_config          ),

    .config_local_mem_slp    (config_local_mem_slp   ),
    .config_local_mem_sd     (config_local_mem_sd    ),
                                                     
    .config_global_mem_slp   (config_global_mem_slp  ),
    .config_global_mem_sd     (config_global_mem_sd    ),
                                                     
    .config_stream_instr_slp (config_stream_instr_slp),
    .config_stream_ld_slp    (config_stream_ld_slp   ),
    .config_stream_st_slp    (config_stream_st_slp   ),
                                                     
    .config_stream_instr_sd  (config_stream_instr_sd ),
    .config_stream_ld_sd     (config_stream_ld_sd    ),
    .config_stream_st_sd     (config_stream_st_sd    ),

    .data_in                   (reg_data[0 +: IO_OUT_L]),
    .data_out                  (out_config),

    .shift_en                  (config_shift_en)   
  );

  io_monitor IO_MONITOR_INS (
    .reg_data         (reg_data         ),
                                        
    .global_rd_req    (monitor_global_rd_req    ),
    .global_rd_gnt    (monitor_global_rd_gnt    ),
    .global_wr_req    (monitor_global_wr_req    ),
    .global_wr_gnt    (monitor_global_wr_gnt    ),
  
    .instr_stream_req (monitor_instr_stream_req ),
    .instr_stream_gnt (monitor_instr_stream_gnt ),
    .ld_stream_req    (monitor_ld_stream_req    ),
    .ld_stream_gnt    (monitor_ld_stream_gnt    ),
    .st_stream_req    (monitor_st_stream_req    ),
    .st_stream_gnt    (monitor_st_stream_gnt    ),
  
    .pe_out           (monitor_pe_out           ),
    .instr            (monitor_instr            ),

    .out              (out_monitor)
  );

  full_design_wo_periphery FULL_DESIGN_WO_PERIPHERY_INS (
    .clk                         (clk                         ),
    .rst                         (rst                         ),

    .config_local_mem_slp    (config_local_mem_slp   ),
    .config_local_mem_sd     (config_local_mem_sd    ),
                                                     
    .config_global_mem_slp   (config_global_mem_slp  ),
    .config_global_mem_sd     (config_global_mem_sd    ),
                                                     
    .config_stream_instr_slp (config_stream_instr_slp),
    .config_stream_ld_slp    (config_stream_ld_slp   ),
    .config_stream_st_slp    (config_stream_st_slp   ),
                                                     
    .config_stream_instr_sd  (config_stream_instr_sd ),
    .config_stream_ld_sd     (config_stream_ld_sd    ),
    .config_stream_st_sd     (config_stream_st_sd    ),
                                                              
    .init_global_mem_addr        (init_global_mem_addr        ),
    .init_global_mem_vld         (init_global_mem_vld         ),
    .init_global_mem_wr_en       (init_global_mem_wr_en       ),
    .init_global_mem_wr_data     (init_global_mem_wr_data     ),
    .init_global_mem_rd_data     (init_global_mem_rd_data     ),
    .init_global_mem_rd_data_vld (init_global_mem_rd_data_vld ),
                                                              
    .init_local_mem_addr         (init_local_mem_addr         ),
    .init_local_mem_wr_data      (init_local_mem_wr_data      ),
    .init_local_mem_vld          (init_local_mem_vld          ),
    .init_local_mem_wr_en        (init_local_mem_wr_en        ),
    .init_local_mem_rd_data      (init_local_mem_rd_data      ),
    .init_local_mem_rd_data_vld  (init_local_mem_rd_data_vld  ),

    .init_stream_wr_data         (init_stream_wr_data    ),
    .init_stream_addr            (init_stream_addr       ),
    .init_stream_wr_vld          (init_stream_wr_vld     ),
    .init_stream_rd_vld          (init_stream_rd_vld     ),
    .init_stream_rd_data         (init_stream_rd_data    ),
    .init_stream_rd_data_vld     (init_stream_rd_data_vld),

    .instr_stream_start_addr_io  (config_instr_stream_start_addr_io),
    .instr_stream_end_addr_io    (config_instr_stream_end_addr_io  ),

    .ld_stream_start_addr_io     (config_ld_stream_start_addr_io),
    .ld_stream_end_addr_io       (config_ld_stream_end_addr_io  ),
                                 
    .st_stream_start_addr_io     (config_st_stream_start_addr_io),
    .st_stream_end_addr_io       (config_st_stream_end_addr_io  ),
                               
    .precision_config            (config_precision_config       ),
                                                         
    .reset_execution_io          (reset_execution_io     ),
    .enable_execution_io         (enable_execution_io    ),
    .done_execution_io           (done_execution_io      ),

    .monitor       (monitor),
    .monitor_global_rd_req (monitor_global_rd_req),
    .monitor_global_rd_gnt (monitor_global_rd_gnt),
    .monitor_global_wr_req (monitor_global_wr_req),
    .monitor_global_wr_gnt (monitor_global_wr_gnt),
    .monitor_instr_stream_req (monitor_instr_stream_req),
    .monitor_instr_stream_gnt (monitor_instr_stream_gnt),
    .monitor_ld_stream_req    (monitor_ld_stream_req   ),
    .monitor_ld_stream_gnt    (monitor_ld_stream_gnt   ),
    .monitor_st_stream_req    (monitor_st_stream_req   ),
    .monitor_st_stream_gnt    (monitor_st_stream_gnt   ),
    .monitor_pe_out(monitor_pe_out),
    .monitor_instr (monitor_instr)
  );


  always_comb begin
    out_pre = out_init;
    if (config_shift_en) begin
      out_pre = out_config;
    end else if (monitor)begin
      out_pre = out_monitor;
    end else begin
      out_pre = out_init;
    end
  end

  assign out = out_pre;
endmodule


`endif //PRU_ASYNC_WO_IO_DEF
