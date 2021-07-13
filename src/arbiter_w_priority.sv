//=======================================================================
// Created by         : KU Leuven
// Filename           : arbiter_w_priority.sv
// Author             : Nimish Shah
// Created On         : 2019-12-11 11:02
// Last Modified      : 
// Update Count       : 2019-12-11 11:02
// Description        : 
//                      
//=======================================================================

`ifndef ARBITER_W_PRIORITY_DEF
  `define ARBITER_W_PRIORITY_DEF

`include "arbiter.sv"

module crossbar_arbiter_w_priority #(
  parameter N_IN_PORTS= 8,
  parameter N_OUT_PORTS= 8
) 
(
  input clk, rst,
  input logic [N_IN_PORTS-1 : 0] req,
  input logic [N_IN_PORTS-1 : 0] [$clog2(N_OUT_PORTS) -1 : 0] req_out_port, // Specifies request is for which output port
  output logic [N_IN_PORTS-1 : 0] grant,

  input [N_OUT_PORTS - 1 : 0] priority_req,
  output [N_OUT_PORTS - 1 : 0] priority_grant,

  output logic [N_OUT_PORTS-1 : 0] grant_out_port_wise,
  output logic [N_OUT_PORTS-1 : 0] [N_IN_PORTS - 1 : 0] detailed_grant,
  output logic [N_OUT_PORTS - 1 : 0][$clog2(N_IN_PORTS) - 1 : 0] granted_requester_id
); 
  
  logic [N_OUT_PORTS - 1 : 0] priority_grant_pre;
  logic [N_IN_PORTS - 1 : 0] grant_to_reqesters;
  logic [N_OUT_PORTS - 1 : 0] grant_out_port_wise_pre;
  logic [N_OUT_PORTS - 1 : 0][N_IN_PORTS - 1 : 0] detailed_grant_pre;
  logic [N_IN_PORTS - 1 : 0][N_OUT_PORTS - 1 : 0] detailed_grant_transposed;

  // one-hot req signal based on req_out_port
  logic [N_IN_PORTS - 1 : 0] [N_OUT_PORTS - 1 : 0]req_based_on_out_port_transposed;
  logic [N_OUT_PORTS - 1 : 0] [N_IN_PORTS - 1 : 0]req_based_on_out_port;
  
  //===========================================
  //      Combinational 
  //===========================================

  // req side
  always_comb begin
    foreach ( req_based_on_out_port_transposed[i]) begin
      if (req[i]) begin
        req_based_on_out_port_transposed[i] = 1<< req_out_port[i];
      end else begin
        req_based_on_out_port_transposed[i] = '0;
      end
    end
  end
  always_comb begin
    foreach ( req_based_on_out_port[i]) begin
      for (integer j=0; j< N_OUT_PORTS ; j=j+1) begin
        req_based_on_out_port[i][j] = req_based_on_out_port_transposed[j][i];
      end
    end
  end

  // grant
  always_comb begin
    foreach ( detailed_grant_transposed[i]) begin
      for (integer j=0; j< N_OUT_PORTS ; j=j+1) begin
        detailed_grant_transposed[i][j] = detailed_grant_pre[j][i];
      end
    end
  end
  always_comb begin
    foreach ( grant_out_port_wise_pre[i]) begin
      if (detailed_grant_pre[i] == 0 && priority_grant_pre[i] == 0) begin
        grant_out_port_wise_pre[i] = 0;
      end else begin
        grant_out_port_wise_pre[i] = 1;
      end
    end
  end
  always_comb begin
    foreach ( grant_to_reqesters[i]) begin
      if (detailed_grant_transposed[i] == 0) begin
        grant_to_reqesters[i] = 0;
      end else begin
        grant_to_reqesters[i] = 1;
      end
    end
  end

  //===========================================
  //      Instances 
  //===========================================
  generate
    genvar out_port_i;
    for (out_port_i=0; out_port_i< N_OUT_PORTS; out_port_i=out_port_i+1) begin: arbiter_loop
      arbiter_w_prority #(.N_IN_PORTS(N_IN_PORTS)) 
        ARBITER_W_PRIORITY_INS (
          .clk          (clk),
          .rst          (rst),
          .req          (req_based_on_out_port[out_port_i]),
          .grant        (detailed_grant_pre   [out_port_i]),
          .granted_requester_id (granted_requester_id[out_port_i]),

          .priority_req (priority_req         [out_port_i]),
          .priority_grant(priority_grant_pre      [out_port_i])
        );
    end
  endgenerate

  assign grant = grant_to_reqesters;
  assign grant_out_port_wise = grant_out_port_wise_pre;
  assign detailed_grant = detailed_grant_pre;
  
  assign priority_grant = priority_grant_pre;

  //===========================================
  //      Assertions 
  //===========================================
  always_ff @(posedge clk ) begin
    foreach ( detailed_grant[i]) begin
      assert property (if (detailed_grant[i] != 0) ($countones(detailed_grant[i]) == 1)) else $warning("one grant at a time");
    end
  end
endmodule



module arbiter_w_prority #(
  parameter N_IN_PORTS= 8
)
(
  input clk, rst,
  input logic [N_IN_PORTS-1 : 0] req,
  output logic [N_IN_PORTS-1 : 0] grant,
  output logic [$clog2(N_IN_PORTS) - 1 : 0] granted_requester_id,

  input priority_req, // Request with highest priority
  output priority_grant
); 
                                     
//===========================================
//      Block diagram 
//===========================================
//
// highest priority    normal priority 
// request             requests        
//         |           | | | | |       
//         |           | | | | |       
//         v           v v v v v       
//     +------------------------------+
//     |   \           | | | | |      |
//     |   |-\         v v v v v      |
//     |   |  -\    +-------------+   |
//     |   |    -\  |     AND     |   |
//     |   |  NOT > |             |   |
//     |   |        +-------------+   |
//     |   |           | | | | |      |
//     |   |           v v v v v      |
//     |   |        +-------------+   |
//     |   |        | normal rr   |   |
//     |   |        | arbitration |   |
//     |   |        +-------------+   |
//     +---|--------------------------+
//         |           | | | | |       
//         v           v v v v v       
//  priority gnt       normal gnts     
                                     
//===========================================
  
  //===========================================
  //      Signals 
  //===========================================
  logic [N_IN_PORTS-1 : 0] gated_req;
  
  assign gated_req = priority_req? '0 : req;

  //===========================================
  //      Instances 
  //===========================================
  simple_rr_arbiter #(
    .N_IN_PORTS(N_IN_PORTS)
  ) SIMPLE_RR_ARBITER_INS (
    .clk  (clk),
    .rst  (rst),
    .req  (gated_req),
    .grant(grant),
    .granted_requester_id(granted_requester_id)
  );

  assign priority_grant = priority_req;

  assert property (@(posedge clk) if (grant != 0) (priority_req == 0)) else $warning("Priority resprected");
  assert property (@(posedge clk) if (grant != 0) (priority_grant == 0)) else $warning("Both cannot be true together");
  assert property (@(posedge clk) if (grant != 0) ($countones(grant) == 1)) else $warning("one grant at a time");
  assert property (@(posedge clk) if (gated_req!= 0) (grant != 0)) else $warning(1);
  assert property (@(posedge clk) if (grant!= 0) (gated_req != 0)) else $warning(1);
endmodule

`endif //ARBITER_W_PRIORITY_DEF
