//=================================================================================================
//  File Name    : HS_Deserializer_tb.v
//  Description  : 
//      This is a SystemVerilog testbench for the HS_Deserializer module.
//      It applies serialized symbol input and verifies correct deserialization
//      into parallel polarity, rotation, and flip signals.
//
//  Test Cases   : 
//      - Reset behavior
//      - Deserialization of a known 7-symbol sequence
//      - Output verification using assertions
//      - Clock synchronization across RxSymClkHS and RxWordClkHS
//
//  Notes        : 
//      - Serialized symbols are fed LSB-fiRstN to simulate transmission
//      - Includes runtime assertion checks for correctness
//      - Displays deserialized values for manual inspection
//
//  Author       : Ahmed Thabit
//  Date         : [01/05/2025]
//=================================================================================================

`timescale 1ns / 1ps

module HS_Deserializer_tb;

    // Inputs
    reg RxSymClkHS;
    reg RstN;
    reg [2:0] SerSym;
    reg HSDeserEn;

    // Outputs
    wire [6:0] RxPolarity;
    wire [6:0] RxRotation;
    wire [6:0] RxFlip;

    // Instantiate DUT
    HS_Deserializer uut (
        .RxSymClkHS(RxSymClkHS),
        .RstN(RstN),
        .SerSym(SerSym),
        .HSDeserEn(HSDeserEn),
        .RxPolarity(RxPolarity),
        .RxRotation(RxRotation),
        .RxFlip(RxFlip)
    );

    // Generate fast symbol clock (e.g. 10ns period)
    initial begin
        RxSymClkHS = 1;
        forever #5 RxSymClkHS = ~RxSymClkHS;
    end
    
   
    // Test stimulus
    initial begin
        $display("----- Starting HS_Deserializer Testbench -----");

        // Initial conditions
        RstN = 0;
        SerSym = 3'b000;
        HSDeserEn = 0;

        // Apply reset
        #50;
        RstN = 1;
        #20;

        // Enable deserialization
        HSDeserEn = 1;

        // Feed in 7 serialized symbols (matching one original parallel word)
        // Let's say original:
        // tx_flip     = 7'b1100_110
        // tx_rotation = 7'b1010_101
        // tx_polarity = 7'b0110_011
        // Feed them LSB-fiRstN

        SerSym = 3'b011;  // bit 0
        #10;
        SerSym = 3'b101;  // bit 1
        #10;
        SerSym = 3'b110;  // bit 2
        #10;
        SerSym = 3'b000; // bit 3
         #10;
        SerSym = 3'b011;  // bit 4
        #10;
        SerSym = 3'b101;  // bit 5
        #10;
        SerSym = 3'b110;  // bit 6
        #10;
        HSDeserEn = 0;
        #1;
        assert (RxPolarity == 7'b0110011) else $error("RxPolarity mismatch: %b expected = b0110011", RxPolarity);
        assert (RxRotation == 7'b1010101) else $error("RxRotation mismatch: %b expected =b1010101", RxRotation);
        assert (RxFlip     == 7'b1100110) else $error("RxFlip mismatch: %b expected =b1100110", RxFlip);

        // Wait for word clock edge to trigger output update
        //#10;

        // Check outputs
        $display("Deserialized Output at time :", $time);
        $display("Test Case 1 Outputs:");
        $display("RxPolarity = %b ", RxPolarity);
        $display("RxRotation = %b", RxRotation);
        $display("RxFlip     = %b", RxFlip);
        


        
        // Expected: 
        // polarity = 0110011
        // rotation = 1010101
        // flip     = 1100110
        
        // Check outputs
        SerSym = 3'b111; #10;
        SerSym = 3'b111; #10;
        SerSym = 3'b111; #10;
        SerSym = 3'b111; #10;
        SerSym = 3'b111; #10;
        SerSym = 3'b111; #10;
        SerSym = 3'b111; #8;


        // Expect no change from previous value or all zeros after reset
        #1;
        assert (RxPolarity == 7'b0000000) else $error("TC2 Fail: RxPolarity changed while disabled.");
        assert (RxRotation == 7'b0000000) else $error("TC2 Fail: RxRotation changed while disabled.");
        assert (RxFlip     == 7'b0000000) else $error("TC2 Fail: RxFlip changed while disabled.");

        $display("Deserialized Output at time :", $time);
        $display("Test Case 2 Outputs:");
        $display("RxPolarity = %b", RxPolarity);
        $display("RxRotation = %b", RxRotation);
        $display("RxFlip     = %b", RxFlip);
        // ===========================
        // TEST CASE 3: Second Data Pattern

        // ===========================
        $display("\n-- Test Case 3: Second Data Pattern --");

        HSDeserEn = 1;

        // Pattern:
        // flip     = 7'b1001101
        // rotation = 7'b0110110
        // polarity = 7'b1110001

        SerSym = 3'b101;  #10;  // bit 0
        SerSym = 3'b001;  #10;  // bit 1
        SerSym = 3'b110;  #10;  // bit 2
        SerSym = 3'b011;  #10;  // bit 3
        SerSym = 3'b101;  #10;  // bit 4
        SerSym = 3'b100;  #10;  // bit 5
        SerSym = 3'b111;  #10;  // bit 6
        HSDeserEn = 0;
        //#100; // Wait for word clock to latch

        // Expected outputs:
        // flip     = 1001101
        // rotation = 0110110
        // polarity = 1110001
        #1;
        assert (RxPolarity == 7'b1110001) else $error("TC3 Fail: RxPolarity = %b, expected 1110001", RxPolarity);
        assert (RxRotation == 7'b0110110) else $error("TC3 Fail: RxRotation = %b, expected 0110110", RxRotation);
        assert (RxFlip     == 7'b1001101) else $error("TC3 Fail: RxFlip = %b, expected 1001101", RxFlip);

        $display("Deserialized Output at time :", $time);
        $display("Test Case 3 Outputs:");
        $display("RxPolarity = %b", RxPolarity);
        $display("RxRotation = %b", RxRotation);
        $display("RxFlip     = %b", RxFlip);
        
        $finish;
    end

endmodule
