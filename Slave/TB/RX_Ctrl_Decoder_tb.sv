`timescale 1ns/1ps

module Rx_Ctrl_Decoder_tb;

    reg A, B, C;
    reg CtrlDecoderEn;
    wire [1:0] CtrlDecoderOut;

    // Instantiate the DUT (Device Under Test)
    Rx_Ctrl_Decoder dut (
        .A(A),
        .B(B),
        .C(C),
        .CtrlDecoderEn(CtrlDecoderEn),
        .CtrlDecoderOut(CtrlDecoderOut)
    );

    initial begin
        $display("Starting Rx_Ctrl_Decoder Testbench...");

        // Test case 1: Decoder disabled
        CtrlDecoderEn = 1'b0;
        A = 1'b0; B = 1'b0; C = 1'b0;
        #1;
        assert(CtrlDecoderOut == 2'b00) else $fatal("Test case 1 failed: Decoder disabled");

        // Test case 2: 3'b111 -> 2'b00 (Rx_stop state)
        CtrlDecoderEn = 1'b1;
        A = 1'b1; B = 1'b1; C = 1'b1;
        #1;
        assert(CtrlDecoderOut == 2'b00) else $fatal("Test case 2 failed");

        // Test case 3: 3'b001 -> 2'b01 (RX_HS request state)
        A = 1'b0; B = 1'b0; C = 1'b1;
        #1;
        assert(CtrlDecoderOut == 2'b01) else $fatal("Test case 3 failed");

        // Test case 4: 3'b000 -> 2'b10 (Rx_HS prepare or Rx_LP_Yield or RX_TA_Rqst)
        A = 1'b0; B = 1'b0; C = 1'b0;
        #1;
        assert(CtrlDecoderOut == 2'b10) else $fatal("Test case 4 failed");

        // Test case 5: 3'b100 -> 2'b11 (Rx_LP request etc.)
        A = 1'b1; B = 1'b0; C = 1'b0;
        #1;
        assert(CtrlDecoderOut == 2'b11) else $fatal("Test case 5 failed");

        // Test case 6: Unexpected combination (e.g., 3'b010)
        A = 1'b0; B = 1'b1; C = 1'b0;
        #1;
        assert(CtrlDecoderOut == 2'b00) else $fatal("Test case 6 failed: unexpected input defaulted");

        $display("All assertions passed!");
        $finish;
    end

endmodule
