//=================================================================================================
//  File Name    : ESC_Deserializer_tb.v
//  Description  : 
//      This is a Verilog testbench for the ESC_Deserializer module.
//      It generates the Escape Mode clock and applies bit-serial input data 
//      to verify correct 8-bit parallel output under enable control.
//
//  Test Cases   : 
//      - Basic 8-bit deserialization of known patterns (e.g., 0xAB, 0xF0)
//      - Bit-by-bit input application with output verification using assertions
//      - Deserializer enable/disable behavior
//      - Output monitoring synchronized to falling edge of RxClkEsc
//
//  Notes        : 
//      - Clock generator simulates RxClkEsc at 100 MHz (10 ns period)
//      - Includes runtime assertions for deserialized output correctness
//      - Monitors deserialization activity with timestamped logging
//
//  Author       : Ahmed Thabit
//  Date         : 05/06/2025
//=================================================================================================

`timescale 1ns / 1ps

module ESC_Deserializer_tb;

    // Inputs
    reg RxClkEsc;
    reg RstN;
    reg SerBit;
    reg EscDeserEn;

    // Output
    wire [7:0] RxEscData;

    // Instantiate the DUT
    ESC_Deserializer uut (
        .RxClkEsc(RxClkEsc),
        .RstN(RstN),
        .SerBit(SerBit),
        .EscDeserEn(EscDeserEn),
        .RxValidEsc(RxValidEsc),
        .RxEscData(RxEscData)
    );

    // Clock generation: 10ns period (100 MHz)
    initial begin
        RxClkEsc = 0;
        forever #5 RxClkEsc = ~RxClkEsc;
    end

    // Test stimulus
    initial begin
        $display("----- Starting ESC_Deserializer Testbench -----");

        // Initial values
        RstN = 0;
        EscDeserEn = 0;
        SerBit = 0;

        // Apply reset
        #14;
        RstN = 1;

        // Test Case 1: Send pattern 10101011 (LSB first)
        $display("Test Case 1: Sending 8'b10101011",$time);
        EscDeserEn = 1;
        send_byte(8'b10101011); // LSB first: 1, 1, 0, 1, 0, 1, 0, 1
        @(negedge RxClkEsc);
        #1;
        // Assertion
        if (RxEscData == 8'b10101011)
            $display("✅ Test Case 1 Passed: RxEscData = %b", RxEscData);
        else
            $error("❌ Test Case 1 Failed: RxEscData = %b, Expected 10101011 at time %0t", RxEscData, $time);
        $display("----- Test Case 1 Complete -----");

        // Test Case 2: Send pattern 11110000 (LSB first)
        $display("Test Case 2: Sending 8'b11110000");
        EscDeserEn = 1;
        send_byte(8'b11110000); // LSB first: 0, 0, 0, 0, 1, 1, 1, 1
        @(negedge RxClkEsc);
        #1;
        // Assertion
        if (RxEscData == 8'b11110000)
            $display("✅ Test Case 2 Passed: RxEscData = %b", RxEscData);
        else
            $error("❌ Test Case 2 Failed: RxEscData = %b, Expected 11110000 at time %0t", RxEscData, $time);
        $display("----- Test Case 2 Complete -----");

        // Test Case 3: Disable deserializer
        $display("Test Case 3: Disabling Deserializer");
        EscDeserEn = 0;
        send_byte(8'b00001111); // Send some data, should be ignored
        @(negedge RxClkEsc);
        #1;
        // Assertion
        if (RxEscData == 8'b00000000)
            $display("✅ Test Case 3 Passed: RxEscData = %b", RxEscData);
        else
            $error("❌ Test Case 3 Failed: RxEscData = %b, Expected 00000000 at time %0t", RxEscData, $time);
        $display("----- Test Case 3 Complete -----");

        // End simulation
        #20;
        $display("----- Testbench Complete -----");
        $finish;
    end

    // Task to send a byte (LSB first)
    task send_byte(input [7:0]data);
        integer i;
        begin
            for (i = 0; i < 8; i = i + 1) begin
                @(posedge RxClkEsc);
                SerBit = data[i]; // Send LSB first
            end
        end
    endtask

endmodule