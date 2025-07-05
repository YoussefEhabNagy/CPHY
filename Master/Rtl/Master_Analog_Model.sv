module Master_Analog_Model (
    input  [1:0] A_PU_PD,
    input  [1:0] B_PU_PD,
    input  [1:0] C_PU_PD,
    input        HsTxEn,
    input  [2:0] LpTx,
    input        LpTxEn,
    input  [2:0] LpRx,
    output reg [7:0] A,
    output reg [7:0] B,
    output reg [7:0] C
);

always @(*) begin
    if(HsTxEn && LpTxEn) begin
        A = 8'd255;
        B = 8'd255;
        C = 8'd255;
    end
    else if(HsTxEn) begin
        case(A_PU_PD)
            2'b00: A = 8'd255;  //Chosen Value to indicate High impedence
            2'b01: A = 8'd0;
            2'b10: A = 8'd40;
            2'b11: A = 8'd20;
            default: A = 8'd255;
        endcase
        case(B_PU_PD)
            2'b00: B = 8'd255;
            2'b01: B = 8'd0;
            2'b10: B = 8'd40;
            2'b11: B = 8'd20;
            default: B = 8'd255;
        endcase
        case(C_PU_PD)
            2'b00: C = 8'd255;
            2'b01: C = 8'd0;
            2'b10: C = 8'd40;
            2'b11: C = 8'd20;
            default: C = 8'd255;
        endcase
    end
    else if (LpTxEn) begin
        A = LpTx[2]*100;
        B = LpTx[1]*100;
        C = LpTx[0]*100;
    end
    else begin
        A = LpRx[2]*100;
        B = LpRx[1]*100;
        C = LpRx[0]*100;
    end
end

endmodule