//=================================================================================================
//  File Name    : Rx_Ctrl_Decoder.v
//  Description  : 
//      This module implements a simple control decoder for C-PHY control signals.
//      It decodes a 3-bit input signal combination (A, B, C) into a 2-bit control output,
//      based on enabled state.
//
//      The decoder interprets input combinations to determine control states such as
//      Rx_stop, Rx_HS_request, bridge state, and Rx_LP_request, facilitating state transitions.
//
//  Key Inputs   :
//      - A, B, C            : 1-bit input signals forming a 3-bit control vector.
//      - CtrlDecoderEn      : Enable signal to activate decoding logic.
//
//  Key Outputs  :
//      - CtrlDecoderOut [1:0] : 2-bit decoded control output.
//
//  Author       : Ahmed
//  Date         : 19/05/2025
//=================================================================================================

`timescale 1ns / 1ps
module Rx_Ctrl_Decoder (
    input wire A,B,C,                    // input signals for the control logic
    input wire  CtrlDecoderEn,               // enable signal for control logic
    output reg [1:0] CtrlDecoderOut         // output signal for control logic
    );


    always @(*) begin
        if (CtrlDecoderEn) begin
            case ({A,B,C})
                 3'b111: CtrlDecoderOut = 2'b00; // any state-> Rx_stop state  
                 3'b001: CtrlDecoderOut = 2'b01; // Stop     -> RX_HS request state
                 3'b000: CtrlDecoderOut = 2'b10; //bridge 
                 3'b100: CtrlDecoderOut = 2'b11; // stop     ->Rx_Lp request state    & RX_LP_Yield state ->RX_TA_Rqst state
                 default:  CtrlDecoderOut = 2'b11;
            endcase
        end else begin
            CtrlDecoderOut = 2'b00; // Default case when decoder is disabled
        end
    end
    endmodule