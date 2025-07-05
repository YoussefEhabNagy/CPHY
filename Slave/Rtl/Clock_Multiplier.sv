//`timescale 1ns/1ps

module Clock_Multiplier (
    input  logic ClkIn,      // input clock
    output logic SymClk = 0  // output clock at 2x frequency
);

    time period;
    time last_rise;
    bit  initialized = 0;

    always @(posedge ClkIn) begin
        if (last_rise != 0) begin
            period = $time - last_rise;
            // Kill any existing clock generation
            disable clock_gen;
            
            fork : clock_gen
                forever begin
                    #(period/4) SymClk = 1'b0;
                    #(period/4) SymClk = 1'b1;
                end
            join_none
        end
        last_rise = $time;
        initialized = 1;
    end

    initial begin
        // Wait for proper initialization
        wait(initialized);
		
        // Safety timeout
        //#100ns $error("Clock initialization failed");
    end

endmodule