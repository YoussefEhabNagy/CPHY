module reg_file #( parameter width = 7) (
   // A simple register file module,
   input wire clk,
   input wire rst_n,
   input wire [width-1:0] data_in,
   output reg [width-1:0] data_out
);

always @(posedge clk or negedge rst_n) begin
    if (!rst_n)
        data_out <= 0; // Reset output to zero on reset
    else
        data_out <= data_in; // Update output with input data on clock edge
end
endmodule