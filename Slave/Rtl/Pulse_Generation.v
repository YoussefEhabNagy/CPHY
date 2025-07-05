`timescale 1ns / 1ps

module Pulse_Generation (
    input A,
    input B,
    input C,
    output reg OutClk
);
    initial begin
        OutClk = 0;
    end
    // Delayed versions of inputs
    wire DelayedA;
    wire DelayedB;
    wire DelayedC;

    // XOR differences between original and delayed inputs
    wire DiffA;
    wire DiffB;
    wire DiffC;

    //Generated pulse
    wire pulse;

    // Delay elements (behavioral, for simulation only)
    assign #1 DelayedA = A;
    assign #1 DelayedB = B;
    assign #1 DelayedC = C;

    //Edge detection
    assign DiffA = A ^ DelayedA;
    assign DiffB = B ^ DelayedB;
    assign DiffC = C ^ DelayedC;

    //Pulse generation
    assign pulse = DiffA | DiffB | DiffC;

    always @(posedge pulse) begin
        OutClk = ~OutClk;     
    end
    
endmodule