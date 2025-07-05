//=================================================================================================
//  File Name    : RxTimer.v
//  Description  : 
//      This module implements a programmable timer used in C-PHY control logic.
//      It counts clock cycles based on a selected timeout value determined by TimerSeed input.
//      When enabled, it increments a counter and asserts a Timeout signal once the count 
//      reaches the predefined timeout threshold.
//
//      The timeout values correspond to timing requirements (in clock cycles) for various 
//      C-PHY protocol timing parameters such as LP_TX_TIME, TERMEN_TIME, SETTLE_TIME, etc.
//
//  Key Inputs   :
//      - clk          : System clock
//      - rst_n        : Active-low reset
//      - TimerEn      : Enable signal for timer counting
//      - TimerSeed[2:0] : Selector for timeout duration
//
//  Key Outputs  :
//      - Timeout      : Asserted when the timer reaches the selected timeout period
//
//  Timing Parameters (Assuming 300 MHz clock, ~3.33 ns period):
//      - LP_TX_TIME    = 15 cycles (~50 ns)
//      - TERMEN_TIME   = 15 cycles (~50 ns)
//      - SETTLE_TIME   = 30 cycles (~100 ns)
//      - TA_SURE_TIME  = 30 cycles (~100 ns)
//      - TA_GET_TIME   = 75 cycles (~250 ns)
//      - WAKE_UP_TIME  = 300 cycles (~1 us)
//
//  Author       : Mohamed Emam
//  Date         : 24/05/2025
//=================================================================================================


module RxTimer (  
    input wire clk,
    input wire rst_n,
    input wire TimerEn,
    input wire [2:0] TimerSeed,
    output reg Timeout
);


// Timer parameters in clock cycles (at 300 MHz -> 3.33 ns period)
parameter LP_TX_TIME     = 15;   // ? 50ns
parameter TERMEN_TIME    = 15;   // ? 50ns 
parameter SETTLE_TIME    = 30;   // ? 100ns
parameter TA_SURE_TIME   = 30;   // ? 100ns
parameter TA_GET_TIME    = 75;   // ? 250ns
parameter WAKE_UP_TIME   = 300;  // ? 1000ns = 1us


reg [15:0] counter;
reg [15:0] timeout_value;

// Combinational logic for selecting timeout value
always @(*) begin
    case (TimerSeed)
        3'b000: timeout_value = LP_TX_TIME;
        3'b001: timeout_value = TERMEN_TIME;
        3'b010: timeout_value = SETTLE_TIME;
        3'b011: timeout_value = TA_SURE_TIME;
        3'b100: timeout_value = TA_GET_TIME;
        3'b101: timeout_value = WAKE_UP_TIME;
        default: timeout_value = 0;
    endcase
end

// Sequential logic for counter
always @(posedge clk or negedge rst_n) begin
    if (!rst_n)
        counter <= 0;
    else if (TimerEn) begin
        if (counter < timeout_value)
            counter <= counter + 1;
        else
            counter <= 0; // Reset counter when timeout is reached
    end else
        counter <= 0;
end


// Sequential logic for Timeout signal
always @(posedge clk or negedge rst_n) begin
    if (!rst_n)
        Timeout <= 0;
    else if (TimerEn && counter >= timeout_value)
        Timeout <= 1;
    else
        Timeout <= 0;
end

endmodule
