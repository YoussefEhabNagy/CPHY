//=================================================================================================
//  File Name    : HS_Serializer_tb.v
//  Description  : 
//      This is a SystemVerilog testbench for the HS_Serializer module.
//      It generates clock signals and applies input stimulus to verify 
//      serialization behavior across polarity, rotation, and flip configurations.
//
//  Test Cases   : 
//      - Basic enable/disable sequence
//      - Serializer behavior with different polarity, rotation, and flip patterns
//      - Clock domain handling (TxWordClkHs and TxSymbolClkHS)
//      - Output verification through monitored signals
//
//  Notes        : 
//      - Uses two separate clock generators for word and symbol clocks
//      - Includes waveform-friendly signal changes and test scenario timing
//      - Prints output values and internal counter for debugging
//
//  Author       : Ahmed Thabit
//  Date         : [01/05/2025]
//=================================================================================================

`timescale 1ns / 1ps
module HS_Serializer_tb;
    // Testbench signals
    reg TxSymbolClkHS;
    reg RstN;
    reg [6:0] TxPolarity;
    reg [6:0] TxRotation;
    reg [6:0] TxFlip;
    reg HsSerializerEn;
    wire [2:0] SerSym;

    // Instantiate DUT
    HS_Serializer uut (
        .TxSymbolClkHS(TxSymbolClkHS),
        .RstN(RstN),
        .TxPolarity(TxPolarity),
        .TxRotation(TxRotation),
        .TxFlip(TxFlip),
        .HsSerializerEn(HsSerializerEn),
        .SerSym(SerSym)
    );


    // Generate TxSymbolClkHS (fast clock, 20ns period = 7x faster)
    initial begin
        TxSymbolClkHS = 1;
        forever #5 TxSymbolClkHS = ~TxSymbolClkHS;
    end

    // Stimulus
    initial begin
        // Initial states
        RstN = 0;
        HsSerializerEn = 0;
        TxPolarity = 7'b0000000;
        TxRotation = 7'b0000000;
        TxFlip     = 7'b0000000;

        // Reset and wait
        #69;
        RstN = 1;

        // Apply test input
        TxPolarity = 7'b1010101;
        TxRotation = 7'b0101010;
        TxFlip     = 7'b1110001;
        HsSerializerEn = 1;
        //apply test input with deassertion for HsSerializerEn
        #70;
        HsSerializerEn = 0;
        TxPolarity = 7'b1111111;
        TxRotation = 7'b0011000;
        TxFlip     = 7'b1100111;
        //assert HsSerializerEn again
        #70;
        HsSerializerEn = 1;
        #70;
        // Change input data
        TxPolarity = 7'b1010101;
        TxRotation = 7'b0101010;
        TxFlip     = 7'b1110010;



        // Let it run for a few symbol clocks
        #1400;

        // Disable serializer
        HsSerializerEn = 0;

        #200;

        $finish;
    end

    // Monitor the output
    initial begin
        $monitor("Time=%0t | SerSym=%b | counter=%0d", $time, SerSym, uut.counter);
    end

endmodule
