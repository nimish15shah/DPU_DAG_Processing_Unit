//=======================================================================
// Created by         : KU Leuven
// Filename           : arbiter.sv
// Author             : Nimish Shah
// Created On         : 2019-12-02 13:57
// Last Modified      : 
// Update Count       : 2019-12-02 13:57
// Description        : 
//                      
//=======================================================================
`ifndef ARBITER_DEF
  `define ARBITER_DEF

module simple_rr_arbiter #(
  parameter N_IN_PORTS = 8
)
(
  input clk, rst,
  input logic [N_IN_PORTS-1 : 0] req,
  output logic [N_IN_PORTS-1 : 0] grant,
  output logic [$clog2(N_IN_PORTS) - 1 : 0] granted_requester_id
);
  // Pointer for highest priority in round-robin arbitration
  logic [$clog2(N_IN_PORTS) -1 : 0] priority_pointer;

  logic [N_IN_PORTS-1 : 0] grant_pre;
  logic [$clog2(N_IN_PORTS) - 1 : 0] granted_requester_id_pre;

  always_ff @(posedge clk or negedge rst) begin
    if (rst== 0) begin
      priority_pointer <= '0;
    end else begin
      if (grant_pre != 0) begin
        priority_pointer <= granted_requester_id_pre + 1; // Currently granted port set to least priority
      end
    end
  end

  programmable_priority_encode #(.N_IN_PORTS(N_IN_PORTS)) programmable_priority_encode_ins (
    .req              (req                 ),
    .priority_pointer (priority_pointer    ),
    .grant            (grant_pre           ),
    .granted_requester(granted_requester_id_pre)
  );

  assign grant = grant_pre;
  assign granted_requester_id = granted_requester_id_pre;

  assert property (@(posedge clk) if (grant != 0) ($countones(grant) == 1)) else $warning("one grant at a time");
  assert property (@(posedge clk) if (req!= 0) (grant != 0)) else $warning(1);
  assert property (@(posedge clk) if (grant!= 0) (req != 0)) else $warning(1);

endmodule

module crossbar_arbiter #(
  parameter N_IN_PORTS= 8,
  parameter N_OUT_PORTS= 8
)
(
  input clk, rst,
  input logic [N_IN_PORTS-1 : 0] req,
  input logic [N_IN_PORTS-1 : 0] [$clog2(N_OUT_PORTS) -1 : 0] req_out_port, // Specifies request is for which output port
  output logic [N_IN_PORTS-1 : 0] grant,

  output logic [N_OUT_PORTS-1 : 0] grant_out_port_wise,
  output logic [N_OUT_PORTS-1 : 0] [N_IN_PORTS - 1 : 0] detailed_grant,
  output logic [N_OUT_PORTS - 1 : 0][$clog2(N_IN_PORTS) - 1 : 0] granted_requester_id

); 
  
  // Pointer for highest priority in round-robin arbitration
  logic [N_OUT_PORTS -1 : 0] [$clog2(N_IN_PORTS) -1 : 0] priority_pointer;
  
  logic [N_IN_PORTS - 1 : 0] grant_to_reqesters;
  logic [N_OUT_PORTS - 1 : 0] grant_out_port_wise_pre;
  logic [N_OUT_PORTS - 1 : 0][$clog2(N_IN_PORTS) - 1 : 0] granted_requester_id_pre;
  logic [N_OUT_PORTS - 1 : 0][N_IN_PORTS - 1 : 0] detailed_grant_pre;
  logic [N_IN_PORTS - 1 : 0][N_OUT_PORTS - 1 : 0] detailed_grant_transposed;

  // one-hot req signal based on req_out_port
  logic [N_IN_PORTS - 1 : 0] [N_OUT_PORTS - 1 : 0]req_based_on_out_port_transposed;
  logic [N_OUT_PORTS - 1 : 0] [N_IN_PORTS - 1 : 0]req_based_on_out_port;

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

  
  always_ff @(posedge clk or negedge rst) begin
    if (rst== 0) begin
      priority_pointer <= '0;
    end else begin
      foreach (priority_pointer[out_port]) begin
        if (grant_out_port_wise_pre[out_port] == 1) begin
          priority_pointer[out_port] <= granted_requester_id_pre[out_port] + 1; // Currently granted port set to least priority
        end
      end
    end
  end
  
  // Instantiate multiple programmable_priority_encode
  generate
    genvar out_port_i;
    for (out_port_i=0; out_port_i< N_OUT_PORTS; out_port_i=out_port_i+1) begin: ppe_loop
      programmable_priority_encode #(.N_IN_PORTS(N_IN_PORTS)) programmable_priority_encode_ins (
        .req              (req_based_on_out_port[out_port_i]),
        .priority_pointer (priority_pointer     [out_port_i]),
        .grant            (detailed_grant_pre       [out_port_i]),
        .granted_requester(granted_requester_id_pre [out_port_i])
      );
    end
  endgenerate

  always_comb begin
    foreach ( detailed_grant_transposed[i]) begin
      for (integer j=0; j< N_OUT_PORTS ; j=j+1) begin
        detailed_grant_transposed[i][j] = detailed_grant_pre[j][i];
      end
    end
  end
  always_comb begin
    foreach ( grant_out_port_wise_pre[i]) begin
      if (detailed_grant_pre[i] == 0) begin
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

  assign grant                = grant_to_reqesters;
  assign grant_out_port_wise  = grant_out_port_wise_pre;
  assign detailed_grant       = detailed_grant_pre;
  assign granted_requester_id = granted_requester_id_pre;

endmodule


module programmable_priority_encode #(
  parameter N_IN_PORTS= 8
)
(
  input [N_IN_PORTS - 1 : 0         ] req,
  input [$clog2(N_IN_PORTS) - 1 : 0 ] priority_pointer,
  output [N_IN_PORTS - 1 : 0        ] grant,
  output [$clog2(N_IN_PORTS) -1 : 0 ] granted_requester
);
  
  logic [2*N_IN_PORTS-1 : 0] req_pre_shift;
  logic [N_IN_PORTS-1 : 0] req_post_shift;

  logic [N_IN_PORTS-1 : 0] grant_out;
  logic [$clog2(N_IN_PORTS) -1 : 0] granted_requester_pre_shift;
  logic [$clog2(N_IN_PORTS) -1 : 0] granted_requester_post_shift;

  
  // Shift inputs
  assign req_pre_shift = {req, req};
  assign req_post_shift = req_pre_shift >> priority_pointer;

  // Static priority encode with highest priority being the 0th inputs
  always_comb begin
    granted_requester_pre_shift= 0;
    for (integer i=N_IN_PORTS -1; i>= 0; i=i-1) begin
      if (req_post_shift[i] == 1) begin
        granted_requester_pre_shift = i;
      end
    end
  end
  
  assign granted_requester_post_shift = granted_requester_pre_shift + priority_pointer;

  assign grant_out = req? (1<< granted_requester_post_shift) : '0; // set grant to 0 if req is 0
  
  // outputs
  assign grant = grant_out;
  assign granted_requester = granted_requester_post_shift;

endmodule

`endif //ARBITER_DEF
