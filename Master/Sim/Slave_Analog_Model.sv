module Slave_Analog_Model (
    input [7:0] A_Wire,
    input [7:0] B_Wire,
    input [7:0] C_Wire,
    input       HsRxEn,
    input       LpRxEn,
    output reg  A,
    output reg  B,
    output reg  C
);

always @(*) begin
    if(HsRxEn) begin
        A = (A_Wire > B_Wire);
        B = (B_Wire > C_Wire);
        C = (C_Wire > A_Wire);
    end
    else if (LpRxEn) begin
        A = A_Wire/100;
        B = B_Wire/100;
        C = C_Wire/100;
    end
    else begin
        A = 0;
        B = 0;
        C = 0;
    end
end

endmodule