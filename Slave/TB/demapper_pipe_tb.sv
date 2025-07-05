//=================================================================================================
//  File Name    : tb_demapper.v
//  Description  : 
//      SystemVerilog testbench for the 'demapper' module. It tests conversion of 7-bit fields 
//      (`RxFlip`, `RxRotation`, `RxPolarity`) back into a 16-bit word (`RxDataHS`) and checks
//      for invalid encodings via `RxInvalidCodeHS`.
//
//  Test Cases   : 
//      - Valid input combinations producing known 16-bit values
//      - Invalid flip code triggering the invalid code flag
//      - Assertions used for pass/fail checking
//
//  Notes        : 
//      - Designed to run with minimal delay between field assignment and checking
//      - Uses both bitwise and hexadecimal representations for validation
//
//  Author       : Ahmed Thabit
//  Date         : [01/05/2025]
//=================================================================================================

`timescale 1ns / 1ps

module tb_demapper;

    // Inputs
    reg [6:0] RxFlip;
    reg [6:0] RxRotation;
    reg [6:0] RxPolarity;
    reg clk;
    reg rst_n;

    // Output
    wire [15:0] RxDataHS;
    wire RxInvalidCodeHS;

    // Instantiate the DUT (Device Under Test)
    demapper uut (
        .RxFlip(RxFlip),
        .RxRotation(RxRotation),
        .RxPolarity(RxPolarity),
        .RxDataHS(RxDataHS),
	.rst_n(rst_n),
	.clk(clk),
        .RxInvalidCodeHS(RxInvalidCodeHS)
    );

    initial begin
    	clk = 1;
    	forever #5 clk = ~clk;
  	end

    initial begin
        $display("----- Starting DEMAPPER Testbench -----");

        // Test case 1
        RxFlip = 7'h00;
        RxRotation = 7'b11;
        RxPolarity = 7'b11;
	rst_n=0;
        #10;
	rst_n=1;
        #1;
        assert(RxDataHS == 16'h000f &&RxInvalidCodeHS == 1'b0) else $error("Test case 1 failed: RxDataHS should be 0x000f.");
        #9;
        if (RxDataHS == 16'h000f && RxInvalidCodeHS == 1'b0) begin
            $display("Test case 1 passed: RxDataHS = %h, RxInvalidCodeHS = %b", RxDataHS, RxInvalidCodeHS);
        end else begin
            $error("Test case 1 failed: Expected RxDataHS = 0x000f, got %h", RxDataHS);
        end
        //put invalid data to check the invalid code output
        RxFlip = 7'h51;
        #1;
         assert(RxInvalidCodeHS == 1'b1)
            else $error("Test case 2 failed: Expected RxInvalidCodeHS = 1, got %b", RxInvalidCodeHS);
        #10;
        if (RxInvalidCodeHS == 1'b1) begin
            $display("Test case 2 passed: RxInvalidCodeHS = %b", RxInvalidCodeHS);
        end else begin
            $error("Test case 2 failed: Expected RxInvalidCodeHS = 1, got %b", RxInvalidCodeHS);
        end
	#9;
        // Test case 2
        RxFlip = 7'h0a;
        RxPolarity = 7'b1111_000;
        RxRotation = 7'b1100110;
        #20;
        assert(RxDataHS == 16'b11_00_11_11_11_01_10_00 && RxInvalidCodeHS == 1'b0) else $error("Test case 2 failed: RxDataHS should be 0xcfd8.");
        
        if (RxDataHS == 16'b11_00_11_11_11_01_10_00 && RxInvalidCodeHS == 1'b0) begin
            $display("Test case 2 passed: RxDataHS = %h, RxInvalidCodeHS = %b", RxDataHS, RxInvalidCodeHS);
        end else begin
            $error("Test case 2 failed: Expected RxDataHS = 0xcfd8, got %h", RxDataHS);
        end
	#9;
        // Test case 3
        RxFlip = 7'h20;
        RxPolarity = 7'b011_0001;
        RxRotation = 7'b0000_111;
        #20;
        assert(RxDataHS == 16'b10_01_00_01_00_10_10_11 && RxInvalidCodeHS == 1'b0) else $error("Test case 3 failed: RxDataHS should be 0x912b.");
        
        if (RxDataHS == 16'b10_01_00_01_00_10_10_11 && RxInvalidCodeHS == 1'b0) begin
            $display("Test case 3 passed: RxDataHS = %h, RxInvalidCodeHS = %b", RxDataHS, RxInvalidCodeHS);
        end else begin
            $error("Test case 3 failed: Expected RxDataHS = 0x912b, got %h", RxDataHS);
        end
	#9;
        // Test case 4
        RxFlip = 7'h42;
        RxPolarity = 7'b110_0101;
        RxRotation = 7'b0000_110;
        #20;
        assert(RxDataHS == 16'b11_01_10_01_00_00_11_01 && RxInvalidCodeHS == 1'b0) else $error("Test case 4 failed: RxDataHS should be 0x912b.");
        
        if (RxDataHS == 16'b11_01_10_01_00_00_11_01 && RxInvalidCodeHS == 1'b0) begin
            $display("Test case 4 passed: RxDataHS = %h, RxInvalidCodeHS = %b", RxDataHS, RxInvalidCodeHS);
        end else begin
            $error("Test case 4 failed: Expected RxDataHS = 0x912b, got %h", RxDataHS);
        end
    end

endmodule

