`timescale 1ns/1ps

module tb_ESC_Serializer;

    reg TxClkEsc = 0;
    reg rst;
    reg [7:0] TxDataEsc;
    reg EscSerEn;
    wire SerBit;
    wire TxReadyEsc;
    wire LastBit;

    // Instantiate the DUT
    ESC_Serializer uut (
        .TxClkEsc(TxClkEsc),
        .rst(rst),
        .TxDataEsc(TxDataEsc),
        .EscSerEn(EscSerEn),
        .TxReadyEsc(TxReadyEsc),
        .LastBit(LastBit),
        .SerBit(SerBit)
    );

    // Clock generation: 10ns period
    always #5 TxClkEsc = ~TxClkEsc;

    // Test case array
    reg [7:0] test_vectors[0:3];
    integer i, bit_index;

    initial begin
        $display("Starting ESC_Serializer test...");

        // Initialize test patterns
        test_vectors[0] = 8'b10101010;
        test_vectors[1] = 8'b11110000;
        test_vectors[2] = 8'b00001111;
        test_vectors[3] = 8'b11001100;

        // Reset sequence
        rst = 0;
        EscSerEn = 0;
        TxDataEsc = 8'b0;
        #20;
        rst = 1;
        #10;

        // Loop through each test case
        for (i = 0; i < 4; i = i + 1) begin
            TxDataEsc = test_vectors[i];
            EscSerEn = 1;

            @(posedge TxClkEsc); // Wait for next clock
            //wait (TxReadyEsc == 1); // Wait for serializer to accept data
            $display("\n--- Test case %0d: TxDataEsc = %b ---", i, TxDataEsc);

            for (bit_index = 0; bit_index < 8; bit_index = bit_index + 1) begin
                
                #1; // Small delay to stabilize signals

                if (SerBit !== TxDataEsc[bit_index])
                    $display("  ERROR: Bit %0d mismatch. Expected: %b, Got: %b at time %t", 
                              bit_index, TxDataEsc[bit_index], SerBit, $time);
                else
                    $display("  Bit %0d OK: SerBit = %b | TxReadyEsc = %b | LastBit = %b at time %t", 
                              bit_index, SerBit, TxReadyEsc, LastBit, $time);

                if (bit_index == 7) begin
                    if (LastBit !== 1)
                        $display("  ERROR: LastBit should be HIGH at final bit. Time: %t", $time);
                    else
                        $display("  LastBit correctly HIGH at time %t", $time);
                end
                @(posedge TxClkEsc);
            end

            // Disable serializer after transmission
            EscSerEn = 0;
            @(posedge TxClkEsc);
            #1;

            if (SerBit !== 0)
                $display("  WARNING: SerBit not cleared after disabling. Got: %b at time %t", SerBit, $time);
            else
                $display("  SerBit cleared as expected at time %t", $time);

            #20; // Idle time between tests
        end

        $display("\nAll test cases completed.");
        $finish;
    end

endmodule
