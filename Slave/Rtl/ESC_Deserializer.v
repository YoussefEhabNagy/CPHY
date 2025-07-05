//=================================================================================================
//  File Name    : ESC_Deserializer.v
//  Description  : 
//      This module implements the Escape Mode deserializer for the C-PHY receiver.
//      It converts incoming serial bits (LSB first) received on the falling edge of RxClkEsc 
//      into a parallel 8-bit data output (RxEscData). 
//
//      The deserialization is controlled by the EscDeserEn signal. When enabled, the module 
//      accumulates 8 serial bits into a shift register. Once a full byte is assembled, it is 
//      output as RxEscData, and RxValidEsc is asserted high for one cycle to indicate validity.
//
//  Key Inputs    : 
//      - RxClkEsc             : Escape mode clock, used on falling edge for sampling
//      - RstN                 : Active-low synchronous reset
//      - SerBit               : Serial input bit stream (LSB first)
//      - EscDeserEn           : Enable signal for deserializer operation
//
//  Key Outputs   : 
//      - RxEscData            : Parallel 8-bit output representing deserialized byte
//      - RxValidEsc           : Output flag asserted when RxEscData is valid
//
//  Author        : Ahmed
//  Date          : 19/5/2025
//=================================================================================================


module ESC_Deserializer (
    input wire RxClkEsc,             // Clock for reading serial data (falling edge)
    input wire RstN,                 // Active-low reset
    input wire SerBit,               // Serial input (LSB first)
    input wire EscDeserEn,           // Enable signal for deserialization
    output reg RxValidEsc,           
    output reg [7:0] RxEscData       // Parallel 8-bit output
);

    reg [7:0] shift_reg ;      // Internal shift register
    reg [2:0] bit_count ;      // 3-bit counter (0 to 7)

    always @(negedge RxClkEsc or negedge RstN) begin
        if (!RstN) begin
            shift_reg  <= 8'b0;
            RxEscData  <= 8'b0;
            bit_count  <= 3'd0;
			RxValidEsc <= 0;
        end else if (EscDeserEn) begin
            if (&(bit_count[2:0]) ) begin
                RxEscData <= {SerBit, shift_reg[6:0]};  // Complete byte ready
                bit_count <= 3'd0;
                shift_reg <= 8'b0; // Reset shift register after reading a byte
				RxValidEsc <= 1;

            end else begin
                bit_count <= bit_count + 1; // Increment bit count on each clock cycle
                shift_reg[bit_count] <= SerBit; // Shift in the serial data on the falling edge of the clock
                RxValidEsc <= 0;

				end
        end else begin
            shift_reg  <= 8'b0;
            RxEscData  <= 8'b0;
            bit_count  <= 3'd0;

           
            end            
        end
	
endmodule
