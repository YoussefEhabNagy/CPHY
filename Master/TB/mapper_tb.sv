//=================================================================================================
//  File Name    : tb_mapper.v
//  Description  : 
//      SystemVerilog testbench for the 'mapper' module. It verifies correct mapping of a 16-bit
//      input (`TxData`) into three separate 7-bit outputs: `TxRotation`, `TxPolarity`, and `TxFlip`.
//
//  Test Cases   : 
//      - Multiple static test vectors applied to TxData
//      - Each output (Rotation, Polarity, Flip) validated using assertions
//      - Displays pass/fail status per test vector
//
//  Notes        : 
//      - Assumes LSB-first bit significance unless specified
//      - Immediate assertion feedback per test case
//
//  Author       : Ahmed Thabit
//  Date         : [01/05/2025]
//=================================================================================================

`timescale 1ns / 1ps

module tb_mapper;

    // Inputs
    reg [15:0] TxData;

    // Outputs
    wire [6:0] TxRotation;
    wire [6:0] TxPolarity;
    wire [6:0] TxFlip;

    // Instantiate the Unit Under Test (UUT)
    mapper uut (
        .TxData(TxData),
        .TxRotation(TxRotation),
        .TxPolarity(TxPolarity),
        .TxFlip(TxFlip)
    );

    initial begin
        TxData = 16'b0000000000001111; // Test case 1
        #10; // Wait for 10 time units
        assert(TxRotation == 7'b11) else $error("Test case 1 failed: TxRotation=%b", TxRotation);
        assert(TxPolarity == 7'b11) else $error("Test case 1 failed: TxPolarity=%b", TxPolarity);
        assert(TxFlip == 7'b0000000) else $error("Test case 1 failed: TxFlip=%b", TxFlip);
        // Display only if all are correct
        if (TxRotation == 7'b11 && TxPolarity == 7'b11 && TxFlip == 7'b0000000) begin
            $display("Test case 1 passed : TxRotation=%b, TxPolarity=%b, TxFlip=%b", TxRotation, TxPolarity, TxFlip);
        end


        #10; // Wait for 10 time units
        TxData = 16'h6025; // Test case 2
        #10; // Wait for 10 time units
        assert(TxRotation == 7'b0001000) else $error("Test case 2 failed: TxRotation=%b", TxRotation);
        assert(TxPolarity == 7'b11) else $error("Test case 2 failed: TxPolarity=%b", TxPolarity);
        assert(TxFlip == 7'b100) else $error("Test case 2 failed: TxFlip=%b", TxFlip);
        // Display only if all are correct
        if (TxRotation == 7'b0001000 && TxPolarity == 7'b11 && TxFlip == 7'b100) begin
            $display("Test case 2 passed : TxRotation=%b, TxPolarity=%b, TxFlip=%b", TxRotation, TxPolarity, TxFlip);
        end

        
        #10; // Wait for 10 time units
        TxData = 16'h912a ; // Test case 3
        #10; // Wait for 10 time units
        assert(TxRotation == 7'b111 ) else $error("Test case 3 failed: TxRotation=%b", TxRotation);
        assert(TxPolarity == 7'b10000) else $error("Test case 3 failed: TxPolarity=%b", TxPolarity);
        assert(TxFlip == 7'b0100000) else $error("Test case 3 failed: TxFlip=%b", TxFlip);
        // Display only if all are correct
        if (TxRotation == 7'b0000111 &&  TxPolarity == 7'b0010000 &&  TxFlip     == 7'b0100000) begin
            $display("Test case 3 passed : TxRotation=%b, TxPolarity=%b, TxFlip=%b", TxRotation, TxPolarity, TxFlip);
        end


        #10; // Wait for 10 time units
        TxData = 16'hc819; // Test case 4
        #10; // Wait for 10 time units
        assert(TxRotation == 7'b1000) else $error("Test case 4 failed: TxRotation=%b", TxRotation);
        assert(TxPolarity == 7'b10001) else $error("Test case 4 failed: TxPolarity=%b", TxPolarity);
        assert(TxFlip == 7'b110) else $error("Test case 4 failed: TxFlip=%b", TxFlip);
        // Display only if all are correct
        if (TxRotation == 7'b0001000 && TxPolarity == 7'b0010001 && TxFlip == 7'b110) begin
            $display("Test case 4 passed : TxRotation=%b, TxPolarity=%b, TxFlip=%b", TxRotation, TxPolarity, TxFlip);
        end


        #10; // Wait for 10 time units
        TxData = 16'hfff0; // Test case 5
        #10; // Wait for 10 time units
        assert(TxRotation == 7'b0101100) else $error("Test case 5 failed: TxRotation=%b", TxRotation);
        assert(TxPolarity == 7'b0101100) else $error("Test case 5 failed: TxPolarity=%b", TxPolarity);
        assert(TxFlip == 7'b1010000) else $error("Test case 5 failed: TxFlip=%b", TxFlip);
        // Display only if all are correct
        if (TxRotation == 7'b0101100 && TxPolarity == 7'b0101100 && TxFlip == 7'b1010000) begin
            $display("Test case 5 passed : TxRotation=%b, TxPolarity=%b, TxFlip=%b", TxRotation, TxPolarity, TxFlip);
        end

        $display("Testbench completed.");
        $finish;
    end

endmodule
