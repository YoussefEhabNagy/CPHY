module Reset_Sync #(
    parameter WIDTH = 1
)(
    input  wire              clk,
    input  wire              RstN,
    output wire [WIDTH-1:0]  sync_out
);
    reg [WIDTH-1:0] sync_ff1, sync_ff2;

    always @(posedge clk or negedge RstN) begin
        if (!RstN) begin
            sync_ff1 <= {WIDTH{1'b0}};
            sync_ff2 <= {WIDTH{1'b0}};
        end else begin
            sync_ff1 <= 1'b1;
            sync_ff2 <= sync_ff1;
        end
    end

    assign sync_out = sync_ff2;
endmodule
