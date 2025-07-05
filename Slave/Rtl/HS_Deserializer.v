//=================================================================================================
//  File Name    : HS_Deserializer.v
//  Description  : 
//      This module implements the High-Speed (HS) deserializer for the C-PHY receiver.
//      It converts a stream of serial 3-bit symbols (SerSym) received on the RxSymClkHS domain
//      into parallel 7-symbol-wide outputs aligned to the RxWordClkHS domain.
//
//      The deserialization process separates the symbol into polarity, rotation, and flip bits,
//      accumulating each field over 7 cycles and then outputting the complete word. This module
//      supports enable control (HSDeserEn) and synchronous reset logic.
//
//  Key Inputs    : 
//      - RxSymClkHS          : High-speed symbol clock for sampling incoming symbols
//      - RxWordClkHS         : Word-level clock (used to interpret parallel outputs downstream)
//      - RstN                : Active-low reset signal
//      - SerSym              : Incoming serialized 3-bit symbol (flip, rotation, polarity)
//      - HSDeserEn           : Enable signal for deserialization
//
//  Key Outputs   : 
//      - RxPolarity          : 7-bit parallel polarity vector (bit 0 = first received)
//      - RxRotation          : 7-bit parallel rotation vector
//      - RxFlip              : 7-bit parallel flip vector
//
//  Author       : Ahmed
//  Date         : 18/5/2025
//=================================================================================================



module HS_Deserializer (
    input wire RxSymClkHS,    // Fast clock for serial-to-parallel conversion
    input wire RstN,          // Synchronous active-low reset
    input wire [2:0] SerSym,  // Serial input (3-bit symbol)
    input wire HSDeserEn,     // Enable deserializer
    output reg [6:0] RxPolarity, // Reconstructed parallel outputs
    output reg [6:0] RxRotation,
    output reg [6:0] RxFlip
);

    reg [6:0] temp_polarity;
    reg [6:0] temp_rotation;
    reg [6:0] temp_flip;
    reg [2:0] counter;

    // Synchronous reset logic (only reacts to posedge RxSymClkHS)
    always @(posedge RxSymClkHS or negedge RstN) begin
        if (!RstN) begin
            counter       <= 0;
            temp_polarity <= 0;
            temp_rotation <= 0;
            temp_flip    <= 0;
            RxPolarity   <= 0;
            RxRotation   <= 0;
            RxFlip       <= 0;
        end 
        else if (HSDeserEn) begin
            if (counter == 6) begin  // After 7 cycles (0-6), update outputs
                // Shift in the last bit
                temp_flip[counter]     <= SerSym[2];
                temp_rotation[counter]  <= SerSym[1];
                temp_polarity[counter]  <= SerSym[0];
                
                // Update outputs on the NEXT clock edge
                RxFlip     <= {SerSym[2],temp_flip[5:0]};
                RxRotation <= {SerSym[1],temp_rotation[5:0]};
                RxPolarity <= {SerSym[0],temp_polarity[5:0]};
                
                counter <= 0;  // Reset counter
            end
            else begin
                // Shift in new bits
                temp_flip[counter]     <= SerSym[2];
                temp_rotation[counter] <= SerSym[1];
                temp_polarity[counter] <= SerSym[0];
                
                counter <= counter + 1;  // Increment only on clock edge
            end
        end

    end


   

endmodule
