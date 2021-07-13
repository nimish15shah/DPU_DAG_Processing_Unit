`ifndef INIT_DEF
  `define INIT_DEF


  `include "common.sv"
  `include "interface.sv"
  import periphery_pkg::*;

class Init;
  
  virtual intf ifc;
  string net= "asia";
  localparam INIT_DEBUG= 0;
  localparam bit_len =32;
  string suffix= "";

  function new(virtual intf i);
    this.ifc= i;
    $value$plusargs("NET_NAME=%s", net);
    $display("Simulating netowrk: %s", net);

    $sformat(this.suffix, "_%0d_%0d_%0d_%0db", 2**LOCAL_MEM_ADDR_L, GLOBAL_MEM_BANK_DEPTH, REGBANK_SIZE, this.bit_len);
    $display(this.suffix);
  endfunction : new

  task reset();
    ifc.cb.in <= 0;
    
    ifc.cb.io_opcode <= IO_OPCODE_NOP;

    ifc.reset_execution_io <= 0;
    ifc.enable_execution_io <= 0;
    
    $display(" ----- Reset Started -----");
    this.ifc.cb.rst <= 0; // Synchronous reset
    ifc.cb.reset_execution_io <= 1;
    repeat (2) @(this.ifc.cb);

    this.ifc.cb.rst <= 1; //release Synchronous reset
    ifc.cb.reset_execution_io <= 0;
    repeat (2) @(this.ifc.cb);
    $display(" ----- Reset Ended   -----"); 
  
  endtask

  task init_data();
    localparam N_INIT_DATA= N_PE * (2**LOCAL_MEM_ADDR_L);
    logic [31 : 0] init_addr;
    logic [31 : 0] init_data;
    logic [31 : 0] out;
    logic  [31 : 0] file_lines[ 0 : N_INIT_DATA - 1 ] [0 : 1];
    
    $readmemh({"./no_backup/new_data/", net, suffix, "_data.txt"}, file_lines);

    // write data
    for (integer i=0; i< N_INIT_DATA; i=i+1) begin
      init_addr= file_lines[i][0];
      init_data= file_lines[i][1];
      if ($isunknown(init_addr)) break;
      init_write(init_addr, init_data);
    end
    
    
    if (INIT_DEBUG) begin
      // Verify by reading data
      for (integer i=0; i< N_INIT_DATA; i=i+1) begin
        init_addr= file_lines[i][0];
        init_data= file_lines[i][1];
        if ($isunknown(init_addr)) break;
        init_read(init_addr, out);
        if(ifc.cb.out != init_data) begin
          $display("Fail! %h %h %h\n", ifc.cb.out, init_data, init_addr);
          $fatal(1);
          $finish;
        end else begin
          assert (!$isunknown(ifc.cb.out));
          if (INIT_DEBUG) $display("Pass! %h %h %h\n", ifc.cb.out, init_data, init_addr);
        end
      end
    end
  endtask : init_data
  
  task init_program();
    localparam N_INIT_DATA= N_PE * (2**stream_pkg::INSTR_STR_ADDR_L);
    logic [31 : 0] init_addr;
    logic [31 : 0] init_data;
    logic [31 : 0] out;
    logic  [31 : 0] file_lines_instr[ 0 : N_INIT_DATA - 1 ] [0 : 1];
    logic  [31 : 0] file_lines_ld[ 0 : N_INIT_DATA - 1 ] [0 : 1];
    logic  [31 : 0] file_lines_st[ 0 : N_INIT_DATA - 1 ] [0 : 1];
    
    $readmemh({"./no_backup/new_data/", net, suffix, "_instr_stream.txt"}, file_lines_instr);
    for (integer i=0; i< N_INIT_DATA; i=i+1) begin
      init_addr = file_lines_instr[i][0];
      init_data = file_lines_instr[i][1];
      if ($isunknown(init_addr)) break;
      init_write(init_addr, init_data);
    end
    if (INIT_DEBUG) begin
      for (integer i=0; i< N_INIT_DATA; i=i+1) begin
        init_addr= file_lines_instr[i][0];
        init_data= file_lines_instr[i][1];
        if ($isunknown(init_addr)) break;
        init_read(init_addr, out);
        if(ifc.cb.out != init_data) begin
          $display("Fail! %h %h %h\n", out, init_data, init_addr);
          $fatal(1);
          $finish;
        end else begin
          if (INIT_DEBUG)$display("Pass! %h %h %h\n", out, init_data, init_addr);
        end
      end
    end
    
    $readmemh({"./no_backup/new_data/", net, suffix, "_ld_stream.txt"}, file_lines_ld);
    for (integer i=0; i< N_INIT_DATA; i=i+1) begin
      init_addr = file_lines_ld[i][0];
      init_data = file_lines_ld[i][1];
      if ($isunknown(init_addr)) break;
      init_write(init_addr, init_data);
    end
    if (INIT_DEBUG) begin
      for (integer i=0; i< N_INIT_DATA; i=i+1) begin
        init_addr= file_lines_ld[i][0];
        init_data= file_lines_ld[i][1];
        if ($isunknown(init_addr)) break;
        init_read(init_addr, out);
        if(ifc.cb.out != init_data) begin
          $display("Fail! %h %h %h\n", out, init_data, init_addr);
          $fatal(1);
          $finish;
        end else begin
          if (INIT_DEBUG) $display("Pass! %h %h %h\n", out, init_data, init_addr);
        end
      end
    end

    $readmemh({"./no_backup/new_data/", net, suffix, "_st_stream.txt"}, file_lines_st);
    for (integer i=0; i< N_INIT_DATA; i=i+1) begin
      init_addr = file_lines_st[i][0];
      init_data = file_lines_st[i][1];
      if ($isunknown(init_addr)) break;
      init_write(init_addr, init_data);
    end
    if (INIT_DEBUG) begin
      for (integer i=0; i< N_INIT_DATA; i=i+1) begin
        init_addr= file_lines_st[i][0];
        init_data= file_lines_st[i][1];
        if ($isunknown(init_addr)) break;
        init_read(init_addr, out);
        if(ifc.cb.out != init_data) begin
          $display("Fail! %h %h %h\n", out, init_data, init_addr);
          $fatal(1);
          $finish;
        end else begin
          if (INIT_DEBUG) $display("Pass! %h %h %h\n", out, init_data, init_addr);
        end
    end
  end

  endtask : init_program

  task init_config();
    localparam N_DATA= N_PE*6 + 1 + ((N_PE/32) * 10);
    logic [31 : 0] shift_in, shift_out;
    logic [31 : 0] file_lines [0 : N_DATA - 1];

    $readmemh({"./no_backup/new_data/", net, suffix, "_config.txt"}, file_lines);

    // shift in
    for (integer i=0; i< N_DATA; i=i+1) begin
      shift_in = file_lines[i];
      if ($isunknown(shift_in)) break;
      reg_shift(shift_in);
      repeat(1) @(this.ifc.cb);
      ifc.cb.io_opcode <= IO_OPCODE_CONFIG_SHIFT_EN;
      repeat(1) @(this.ifc.cb);
      ifc.cb.io_opcode <= IO_OPCODE_NOP;
    end
    repeat(1) @(this.ifc.cb);
    
    if (INIT_DEBUG) begin
      // shift out and check
      repeat(1) @(this.ifc.cb);
      for (integer i=0; i< N_DATA; i=i+1) begin
        shift_in = file_lines[i];
        if ($isunknown(shift_in)) break;
        reg_shift(shift_in);
        repeat(1) @(this.ifc.cb);
        ifc.cb.io_opcode <= IO_OPCODE_CONFIG_SHIFT_EN;
        repeat(1) @(this.ifc.cb);

        if(ifc.cb.out != file_lines[i]) begin
          $display("Fail! %h %h %d\n", ifc.cb.out, file_lines[i], i);
          //$fatal(1);
          //$finish;
        end else begin
          assert (!$isunknown(ifc.cb.out));
          if (INIT_DEBUG) $display("Pass! %h %h %d\n", ifc.cb.out, file_lines[i], i);
        end
        ifc.cb.io_opcode <= IO_OPCODE_NOP;
      end
      repeat(1) @(this.ifc.cb);

      // shift in
      for (integer i=0; i< N_DATA; i=i+1) begin
        shift_in = file_lines[i];
        if ($isunknown(shift_in)) break;
        reg_shift(shift_in);
        repeat(1) @(this.ifc.cb);
        ifc.cb.io_opcode <= IO_OPCODE_CONFIG_SHIFT_EN;
        repeat(1) @(this.ifc.cb);
        ifc.cb.io_opcode <= IO_OPCODE_NOP;
      end
      repeat(1) @(this.ifc.cb);
    end
  endtask : init_config

  task init_write(input logic [31 : 0] addr, input logic [31 : 0] data);
    reg_shift(addr);
    reg_shift(data);

    ifc.cb.io_opcode <= IO_OPCODE_WR_EN;
    repeat(1) @(this.ifc.cb);
    ifc.cb.io_opcode <= IO_OPCODE_NOP;

    if (INIT_DEBUG) $display("Write %h %h", data, addr);
  endtask : init_write

  task init_read(input logic [31 : 0] addr, output logic [31 : 0] out_data);
    ifc.cb.io_opcode <= IO_OPCODE_REG_SHIFT_EN;

    ifc.cb.in <= addr [INPUT_DATA_L +: INPUT_DATA_L];
    repeat (1) @(this.ifc.cb);

    ifc.cb.in <= addr [0 +: periphery_pkg::INPUT_DATA_L];
    repeat (1) @(this.ifc.cb);
    repeat (1) @(this.ifc.cb);
    repeat (1) @(this.ifc.cb);

    ifc.cb.io_opcode <= IO_OPCODE_RD_EN;
    repeat(1) @(this.ifc.cb);
    ifc.cb.io_opcode <= IO_OPCODE_NOP;
    repeat(1) @(this.ifc.cb);
    
    out_data = ifc.cb.out;
  endtask : init_read

  task execute(input real CLK_PERIOD);
    time start_time;
    time end_time;
    time run_time;
    
    int rand_delay;
    std::randomize(rand_delay) with {
      rand_delay < 100;
      rand_delay > 2;
    };

    ifc.cb.reset_execution_io <= 1;
    repeat(1) @(this.ifc.cb);
    ifc.cb.reset_execution_io <= 0;
    
    $display("Starting execution!\n");
    start_time= $time;
    repeat(1) @(this.ifc.cb);
    
    ifc.cb.enable_execution_io <= 1;

    //// Randomly disable execution;
    //repeat(rand_delay) @(this.ifc.cb);
    //ifc.cb.enable_execution_io <= 0;
    //repeat(20) @(this.ifc.cb);
    //ifc.cb.enable_execution_io <= 1;
    
    //repeat(N_PE * (2**(stream_pkg::INSTR_STR_ADDR_L))) @(this.ifc.cb);
    //repeat(2000) @(this.ifc.cb);
    //$finish;
    
    fork
      begin
        forever begin
          repeat(10) @(this.ifc.cb);
          $display("cycles: %.2f", (($time - start_time)/CLK_PERIOD));
        end
      end
      begin
        @(ifc.cb iff ifc.cb.done_execution_io);
      end
    join_any

    ifc.cb.enable_execution_io <= 0;

    end_time= $time;
    run_time = end_time - start_time;
    repeat(1) @(this.ifc.cb);

    $display("########################");
    $display("Done execution!");
    $display("########################");
    $display("\n");
    $display("Time statistics: ");

    $display("clk cycles, start time, end time, run_time: %.2f %t, %t, %t\n", (run_time/CLK_PERIOD), start_time, end_time, run_time);
  endtask : execute


  task check_final_output();
    logic [31: 0] addr, golden_out, out;
    logic  [31 : 0] file_lines[0 : 0] [0 : 1];

    $readmemh({"./no_backup/new_data/", net, suffix, "_golden.txt"}, file_lines);
    addr= file_lines[0][0];
    golden_out= file_lines[0][1];

    init_read(addr, out);
    
    assert (!$isunknown(golden_out));
    assert (!$isunknown(out));
    assert (!$isunknown(addr));

    if ((golden_out < out + 2**10) && (golden_out > out - 2**10)) begin
      $display("golden: %h, actual: %h", golden_out, out);
      $display("Test passes  !!!!!");
    end else begin
      $display("golden: %h, actual: %h", golden_out, out);
      $display("########################");
      $display("Test Fail Fail Fail Fail Fail");
      $display("########################");
    end
  endtask : check_final_output

  task reg_shift([31 : 0] data);
    ifc.cb.io_opcode <= IO_OPCODE_REG_SHIFT_EN;

    ifc.cb.in <= data [INPUT_DATA_L +: INPUT_DATA_L];
    repeat (1) @(this.ifc.cb);
    ifc.cb.in <= data [0 +: INPUT_DATA_L];
    repeat (1) @(this.ifc.cb);
    ifc.cb.io_opcode <= IO_OPCODE_NOP;
  endtask : reg_shift

endclass : Init


`endif //INIT_DEF
