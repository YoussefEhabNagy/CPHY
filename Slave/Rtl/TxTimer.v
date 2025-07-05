
module TxTimer (
    input wire clk,
    input wire rst_n,
    input wire TimerEn,
    input wire TimerSeed,
    output reg Timeout
);

// Timer parameters in clock cycles (assuming 3.33ns clock period)
parameter LP_TX_or_Prepare_TIME   = 14;    // 50ns
parameter TA_Go_TIME              = 29;   // 100ns
//decrement by one to compensate timeout signal latency between fsm and timer

reg [15:0] counter;
reg [15:0] timeout_value;

always @(*) begin
    case (TimerSeed)
        1'b0: timeout_value = LP_TX_or_Prepare_TIME;
        1'b1: timeout_value = TA_Go_TIME;
        default: timeout_value = 0;
    endcase
end

always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        counter <= 1;
        Timeout <= 0;
    end else begin
        if (TimerEn) begin
            if (counter >= timeout_value) begin
                Timeout <= 1;
                counter <= 0;
            end else begin
                Timeout <= 0;
                counter <= counter + 1;
            end
        end else begin
            Timeout <= 0;
            counter <= 1; //counter starts one ahead to compensate enable signal latency between fsm and timer
        end
    end
end
endmodule
