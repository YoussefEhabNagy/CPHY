//=================================================================================================
//  File Name    : HS_Sequencer.v
//  Description  : 
//      This module generates the predefined high-speed (HS) sequences used during the C-PHY
//      HS transmission initialization process. It produces the preamble, sync, and post 
//      sequences required before and after transmitting actual HS data, each represented by 
//      specific 3-phase symbols.
//
//      The sequencer advances through the HS sequences based on the control field `HsSeqCtr`,
//      using an internal counter to manage sequence lengths. It signals completion of each stage 
//      (Pre, Post) via `SeqDone`, and ensures correct sequencing and timing by driving 
//      `SeqSym` outputs at each symbol clock cycle.
//
//  Key Inputs    : 
//      - RstN           : Active-low reset
//      - TxSymbolClkHS  : High-speed symbol clock
//      - HsSeqEn        : Enable for sequence generation
//      - TxRequestHS    : Request to begin HS transmission
//      - HsSeqCtr       : Selects sequence (Pre, Sync, Post)
//
//  Key Outputs   : 
//      - SeqDone        : Flags indicating completion of each sequence phase
//      - SeqSym         : 3-bit output symbol to be encoded by the encoder
//
//  Author       : Youssef Ehab
//  Date         : 30/5/2025
//=================================================================================================


module HS_Sequencer (
    input            RstN,
    input            TxSymbolClkHS,
    input            TxReqHS,
    input      [2:0] HsSeqCtr,
    output reg       SeqDone,  
    output reg [2:0] SeqSym
);

wire       Sync;
wire       Post;
wire       Preamble;
reg        Sym4;
reg  [2:0] SeqSymIntermidiate;
reg  [6:0] Count;

assign {Preamble,Sync,Post} = HsSeqCtr;

always @(posedge TxSymbolClkHS, negedge RstN) begin
    if (!RstN) begin
        SeqDone <= 1'b0;
        SeqSym  <= 3'b011;
        Count   <= 7'b0001;
        Sym4    <= 1'b0;
    end
    else begin
        if (Preamble) begin                                      /// Preamble /// 
            if ((Count[6] && Count[5] && Count[4] && Count[3] && Count[2] && !Count[1] && Count[0])) begin   // 1111101 -> 125   to give suffeciecnt amount of preample symbols then sync word then done is asserted
                SeqDone   <= 1'b1;
                Sym4      <= Sym4;      
            end else if ((Count[6] && Count[5] && Count[4] && !Count[3] && Count[2] && Count[1] && Count[0])) begin   // 1110111 -> 119 // to send 4s of the sync after the preample
                SeqDone   <= 1'b0;
                Sym4      <= 1'b1;
            end else if ((Count[6] && Count[5] && Count[4] && Count[3] && Count[2] && !Count[1] && !Count[0])) begin   // 1111100 -> 124 // to send the last 3
                SeqDone   <= 1'b0;
                Sym4      <= 1'b0;
            end else begin
                SeqDone   <= 1'b0;
                Sym4      <= Sym4;
            end
            Count      <= Count + 7'd1;
            if(Sym4)
                SeqSym     <= 3'b100;
            else
                SeqSym     <= 3'b011;


        end
        else if (Sync) begin                                      /// Sync ///

            if (!(|(Count))) begin //Count == 0
                Count      <= Count + 7'd1;
                SeqSym     <= 3'b011;
            end else if ((!Count[6] && !Count[5] && !Count[4] && !Count[3] && Count[2] && Count[1] && !Count[0])) begin   // 0000110 -> 6
                Count      <= 7'd0;
                SeqSym     <= 3'b011;
            end else begin
                Count      <= Count + 7'd1;
                SeqSym     <= 3'b100;
            end
            SeqDone   <= 1'b0;
            Sym4    <= 1'b0;

        end
        else if (Post) begin                            /// Post ///

            if ((!Count[6] && !Count[5] && !Count[4] && !Count[3] && Count[2] && !Count[1] && !Count[0])) begin   // 0000100 -> 4
                Count      <= 7'd0;
                SeqDone   <= 1'b1;
            end else begin
                Count      <= Count + 7'd1;
                SeqDone   <= 1'b0;
            end
            SeqSym     <= 3'b100;
            Sym4    <= 1'b0;

        end
        else begin
            SeqDone   <= 1'b0;
            SeqSym     <= SeqSymIntermidiate;
            Count      <= 7'b0001;
            Sym4    <= 1'b0;
        end 
    end
end

//To set the default value of the Sequencer based on the TxRequestHS, To avoid the first redundunt symbol
always @(*) begin
    SeqSymIntermidiate = (TxReqHS == 1)? 3'b011 : 3'b100;
end

endmodule
