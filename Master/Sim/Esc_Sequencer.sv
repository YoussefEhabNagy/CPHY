//=================================================================================================
//  File Name    : Esc_Sequencer.v
//  Description  : 
//      This module generates the Escape Mode (ESC) commands used in C-PHY low-power
//      (LP) operations. Each ESC command is an 8-bit predefined pattern, serialized bit by bit
//      at the low-speed clock (TxClkEsc) during the command transmission phase.
//
//      The module selects one of eight possible command sequences based on `EscSeqCtr` and 
//      shifts out the corresponding bits sequentially on `SeqBit`. It asserts `CmdDone` when 
//      the full 8-bit command has been transmitted.
//
//  Key Inputs    : 
//      - RstN         : Active-low reset
//      - TxClkEsc     : Clock used for ESC command transmission
//      - EscSeqEn     : Enable signal for command sequencing
//      - EscSeqCtr    : Selector for which ESC command to transmit
//
//  Key Outputs   : 
//      - SeqBit       : Serialized bit output representing the ESC command
//      - CmdDone      : High signal indicating completion of the ESC command
//
//  Author       : Youssef Ehab 
//  Date         : 5/5/2025
//=================================================================================================


module Esc_Sequencer (
    input            RstN,
    input            TxClkEsc,
    input      [7:0] EscSeqCtr,
    output reg       SeqBit,
    output reg       CmdDone
);

reg [2:0] Count;


// Command sequences
wire [0:7] CMD [0:7];
assign CMD[0] = 8'b10001101;        //11100001
assign CMD[1] = 8'b00111001;        //00011110
assign CMD[2] = 8'b11010001;        //10011111
assign CMD[3] = 8'b00101110;        //11011110
assign CMD[4] = 8'b00101110;        //01100010
assign CMD[5] = 8'b00101110;        //01011101
assign CMD[6] = 8'b00011110;        //00100001
assign CMD[7] = 8'b01100101;        //10100000


always @(posedge TxClkEsc, negedge RstN) begin
    if (!RstN) begin
        SeqBit  <= 1'b0;
        CmdDone <= 1'b0;
        Count   <= 3'd0;
    end
    else begin
        if (|(EscSeqCtr)) begin
            if(EscSeqCtr == 7'b1) begin
                if (Count == 3'd5) begin
                    CmdDone <= 1'b1;
                end else begin
                    CmdDone <= 1'b0;
                end
            end
            else begin
                if (Count == 3'd5) begin
                    CmdDone <= 1'b1;
                end else begin
                    CmdDone <= 1'b0;
                end
            end
            SeqBit  <= (|(CMD[Count] & EscSeqCtr));
            Count   <= Count + 3'd1;
        end
        else begin
            SeqBit  <= 1'b0;
            CmdDone <= 1'b0;
            Count   <= 3'd0;
        end
    end
end

endmodule
