module sync_level #(
    parameter WIDTH = 1
)(
    input  wire              clk_dst,
    input  wire              RstN,
    input  wire [WIDTH-1:0]  async_in,
    output wire [WIDTH-1:0]  sync_out
);
    reg [WIDTH-1:0] sync_ff1, sync_ff2;

    always @(posedge clk_dst or negedge RstN) begin
        if (!RstN) begin
            sync_ff1 <= {WIDTH{1'b0}};
            sync_ff2 <= {WIDTH{1'b0}};
        end else begin
            sync_ff1 <= async_in;
            sync_ff2 <= sync_ff1;
        end
    end

    assign sync_out = sync_ff2;
endmodule
