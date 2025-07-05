//=================================================================================================
//  File Name    : Decoder.v
//  Description  : 
//      This module implements the data symbol decoder for the C-PHY receiver path. It decodes
//      high-speed transition sequences into 3-bit symbol values based on current and previous
//      link states received from the C-PHY lane.
//
//      The decoder tracks two successive states (`CS` and `PS`) and determines the corresponding
//      symbol using phase rotation and polarity detection rules defined by the C-PHY protocol.
//      This enables proper interpretation of the serialized data stream after clock recovery.
//
//  Key Inputs    : 
//      - reset               : Asynchronous reset signal
//      - DecoderEn           : Enable signal for decoding logic
//      - RxSymbolClkHS       : Symbol clock used to sample input states
//      - State               : 3-bit representation of current link state
//
//  Key Outputs   : 
//      - Sym                 : Decoded 3-bit symbol corresponding to transition between states
//
//  Author       : Youssef
//  Date         : 18/5/2025
//=================================================================================================


module Decoder(
    input            reset,
    input            DecoderEn,
    input            RxSymbolClkHS,
    input      [2:0] State,
    output reg [2:0] Sym
);

reg [2:0] CS; //Current State
reg [2:0] PS; //Prev.   State

//Data Sampler
always @(posedge RxSymbolClkHS, negedge reset) begin
    if(!reset) begin
        CS <= 3'b000;
        PS <= 3'b000;
    end
    else begin
        if(!DecoderEn) begin
            CS <= 3'b000;
            PS <= 3'b000;
        end
        else begin
            PS <= CS;
            CS <= State;
        end
    end
end

always @(*) begin
    //3 first for preamble then 4 for sync word and post
    if(CS == ~{PS[0],PS[2:1]})      Sym = 3'b011; //Rotate CCW, Opposite Polarity 
    else if(CS == ~PS)              Sym = 3'b100; //Same phase, Opposite polarity
    else if(CS == {PS[1:0],PS[2]})  Sym = 3'b000; //Rotate CCW, Same Polarity
    else if(CS == ~{PS[1:0],PS[2]}) Sym = 3'b001; //Rotate CCW, Opposite Polarity
    else if(CS == {PS[0],PS[2:1]})  Sym = 3'b010; //Rotate CW, Same Polarity
    
    else                            Sym = 3'b011;
end



endmodule
