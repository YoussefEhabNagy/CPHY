module mapper (
    input wire [15:0] TxData,
    output reg [6:0] TxRotation,
    output reg [6:0] TxPolarity,
    output reg [6:0] TxFlip
);

wire mux0,muxa1,muxa2,muxa3,muxa4,muxa5,muxa6,muxb1,muxb2,muxb3,muxb4,muxb5,muxb6;
reg [12:0] mux_values;
assign {muxb6,muxa6,muxb5,muxa5,muxb4,muxa4,muxb3,muxa3,muxb2,muxa2,muxb1,muxa1,mux0}=mux_values;

always@(*)
    begin
                    ////code for muxs values and flip signals//////////
        if(TxData[15:10]>=6'h00 &&TxData[15:10] <=6'h0f) begin
        
            mux_values = 13'b10_10_10_10_10_01_0;
            TxFlip = 7'h00;
        end
        else if (TxData[15:10]>=6'h10 &&TxData[15:10] <=6'h13) begin
                 mux_values=13'b 01_01_01_01_01_00_1;
                 TxFlip=7'h01;
        end
        else if (TxData[15:10]>=6'h14 &&TxData[15:10] <=6'h17) begin
                 mux_values=13'b 01_01_01_01_01_10_0;
                 TxFlip=7'h02;
        end
        else if (TxData[15:10]>=6'h18 &&TxData[15:10] <=6'h1b) begin
                 mux_values=13'b 01_01_01_01_11_01_0;
                 TxFlip=7'h04;
        end
         else if (TxData[15:10]>=6'h1c &&TxData[15:10] <=6'h1f) begin
                 mux_values=13'b 01_01_01_11_10_01_0;
                 TxFlip=7'h08;
        end
         else if (TxData[15:10]>=6'h20 &&TxData[15:10] <=6'h23) begin
                 mux_values=13'b 01_01_11_10_10_01_0;
                 TxFlip=7'h10;
        end
         else if (TxData[15:10]>=6'h24 &&TxData[15:10] <=6'h27) begin
                 mux_values=13'b 01_11_10_10_10_01_0; 
                 TxFlip=7'h20;
        end
        else if (TxData[15:10]>=6'h28 &&TxData[15:10] <=6'h2B) begin
                 mux_values=13'b 11_10_10_10_10_01_0; 
                 TxFlip=7'h40;
        end
        else 
        case(TxData[15:10])
            6'h2c: begin
                mux_values=13'b 00_00_00_00_00_10_1;
                TxFlip=7'h03;
            end
            6'h2d: begin
                mux_values=13'b 00_00_00_00_11_00_1;
                TxFlip=7'h05;
            end
            6'h2e: begin
                mux_values=13'b 00_00_00_11_01_00_1;
                TxFlip=7'h09;
            end
            6'h2f: begin
                mux_values=13'b 00_00_11_01_01_00_1;
                TxFlip=7'h11;
            end
            6'h30: begin
                mux_values=13'b 00_11_01_01_01_00_1;
                                 
                TxFlip=7'h21;
            end
            6'h31: begin
                mux_values=13'b 11_01_01_01_01_00_1;
                TxFlip=7'h41;
            end
            6'h32: begin
                mux_values=13'b 00_00_00_00_11_10_0;
                TxFlip=7'h06;
            end
            6'h33: begin
                mux_values=13'b 00_00_00_11_01_10_1;
                TxFlip=7'h0a;
            end
            6'h34: begin
                mux_values=13'b 00_00_11_01_01_10_0;
                TxFlip=7'h12;
            end
            6'h35: begin
                mux_values=13'b 00_11_01_01_01_10_0;
                TxFlip=7'h22;
            end
            6'h36: begin
                mux_values=13'b 11_01_01_01_01_10_0;
                TxFlip=7'h42;
            end
            6'h37: begin
                mux_values=13'b 00_00_00_11_11_01_0;
                TxFlip=7'h0c;
            end
            6'h38: begin
                mux_values=13'b 00_00_11_01_11_01_0;
                TxFlip=7'h14;
            end
            6'h39: begin
                mux_values=13'b 00_11_01_01_11_01_0;
                TxFlip=7'h24;
            end
            6'h3a: begin
                mux_values=13'b 11_01_01_01_11_01_0;
                TxFlip=7'h44;
            end
            6'h3b: begin
                mux_values=13'b 00_00_11_11_10_01_0;
                TxFlip=7'h18;
            end
            6'h3c: begin
                mux_values=13'b 00_11_01_11_10_01_0;
                TxFlip=7'h28;
            end
            6'h3d: begin
                mux_values=13'b 11_01_01_11_10_01_0;
                TxFlip=7'h48;
            end
            6'h3e: begin
                mux_values=13'b 00_11_11_10_10_01_0;
                TxFlip=7'h30;
            end
            6'h3f: begin
                mux_values=13'b 11_01_11_10_10_01_0;
                TxFlip=7'h50;
            end
            default: begin
                mux_values=13'b 00_00_00_00_00_00_0;
                TxFlip=7'h00;
            end
    endcase

    ////code for TxPolarity and TxRotation signals/////////
    if (!mux0) begin
        TxPolarity[0] = TxData[0];
        TxRotation[0] = TxData[1];
    end else begin
        TxPolarity[0] = 1'b0;
        TxRotation[0] = 1'b0;
    end
    case({muxb1,muxa1})
        2'b00: begin
            TxPolarity[1] = TxData[0];
            TxRotation[1] = TxData[1];
        end
        2'b01: begin
            TxPolarity[1] = TxData[2];
            TxRotation[1] = TxData[3];
        end
        2'b10: begin
            TxPolarity[1] = 1'b0;
            TxRotation[1] = 1'b0;
        end
        default: begin
            TxPolarity[1] = 1'b0;
            TxRotation[1] = 1'b0;
        end
    endcase
    case({muxb2,muxa2})
        2'b00: begin
            TxPolarity[2] = TxData[0];
            TxRotation[2] = TxData[1];
        end
        2'b01: begin
            TxPolarity[2] = TxData[2];
            TxRotation[2] = TxData[3];
        end
        2'b10: begin
            TxPolarity[2] = TxData[4];
            TxRotation[2] = TxData[5];
            end
        2'b11: begin
            TxPolarity[2] = 1'b0;
            TxRotation[2] = 1'b0;
        end
        default: begin
            TxPolarity[2] = 1'b0;
            TxRotation[2] = 1'b0;
        end
    endcase
    case({muxb3,muxa3})
        2'b00: begin
            TxPolarity[3] = TxData[2];
            TxRotation[3] = TxData[3];
        end
        2'b01: begin
            TxPolarity[3] = TxData[4];
            TxRotation[3] = TxData[5];
        end
        2'b10: begin
            TxPolarity[3] = TxData[6];
            TxRotation[3] = TxData[7];
        end
        2'b11: begin
            TxPolarity[3] = 1'b0;
            TxRotation[3] = 1'b0;
        end
        default: begin
            TxPolarity[3] = 1'b0;
            TxRotation[3] = 1'b0;
        end
        endcase
    case({muxb4,muxa4})
        2'b00: begin
            TxPolarity[4] = TxData[4];
            TxRotation[4] = TxData[5];
        end
        2'b01: begin
            TxPolarity[4] = TxData[6];
            TxRotation[4] = TxData[7];
        end
        2'b10: begin
            TxPolarity[4] = TxData[8];
            TxRotation[4] = TxData[9];
        end
        2'b11: begin
            TxPolarity[4] = 1'b0;
            TxRotation[4] = 1'b0;
        end
        default: begin
            TxPolarity[4] = 1'b0;
            TxRotation[4] = 1'b0;
        end
    endcase
    case({muxb5,muxa5})
        2'b00: begin
            TxPolarity[5] = TxData[6];
            TxRotation[5] = TxData[7];
        end
        2'b01: begin
            TxPolarity[5] = TxData[8];
            TxRotation[5] = TxData[9];
        end
        2'b10: begin
            TxPolarity[5] = TxData[10];
            TxRotation[5] = TxData[11];
        end
        2'b11: begin
            TxPolarity[5] = 1'b0;
            TxRotation[5] = 1'b0;
        end
        default: begin
            TxPolarity[5] = 1'b0;
            TxRotation[5] = 1'b0;
        end
    endcase
    case({muxb6,muxa6})
        2'b00: begin
            TxPolarity[6] = TxData[8];
            TxRotation[6] = TxData[9];
        end
        2'b01: begin
            TxPolarity[6] = TxData[10];
            TxRotation[6] = TxData[11];
        end
        2'b10: begin
            TxPolarity[6] = TxData[12];
            TxRotation[6] = TxData[13];
        end
        2'b11: begin
            TxPolarity[6] = 1'b0;
            TxRotation[6] = 1'b0;
        end
        default: begin
            TxPolarity[6] = 1'b0;
            TxRotation[6] = 1'b0;
        end
    endcase
    end

endmodule