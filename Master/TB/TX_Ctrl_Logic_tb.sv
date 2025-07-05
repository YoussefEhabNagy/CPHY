`timescale 1ns/1ps

module TX_Ctrl_Logic_tb;

    reg [1:0] TX_Ctrl_Out;
    wire A, B, C;

    // Instantiate the DUT (Device Under Test)
    TX_Ctrl_Logic dut (
        .TX_Ctrl_Out(TX_Ctrl_Out),
        .A(A),
        .B(B),
        .C(C)
    );

    initial begin
        $display("Starting TX_Ctrl_Logic Testbench...");

        // Test case 1: TX_Ctrl_Out = 2'b00 (Tx_stop state)
        TX_Ctrl_Out = 2'b00;
        #1;
        assert(A == 1'b1 && B == 1'b1 && C == 1'b1) else $display("Test case 1 failed");

        // Test case 2: TX_Ctrl_Out = 2'b01 (Tx_Esc Request state & TX_HS request state)
        TX_Ctrl_Out = 2'b01;
        #1;
        assert(A == 1'b0 && B == 1'b0 && C == 1'b1) else $display("Test case 2 failed");

        // Test case 3: TX_Ctrl_Out = 2'b10 (Lp yield state & others)
        TX_Ctrl_Out = 2'b10;
        #1;
        assert(A == 1'b0 && B == 1'b0 && C == 1'b0) else $display("Test case 3 failed");

        // Test case 4: TX_Ctrl_Out = 2'b11 (Lp Request & turn around request)
        TX_Ctrl_Out = 2'b11;
        #1;
        assert(A == 1'b1 && B == 1'b0 && C == 1'b0) else $display("Test case 4 failed");

       
        $finish;
    end

endmodule
