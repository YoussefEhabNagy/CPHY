module Mux_1Bit (
    input  wire A,     // Input A
    input  wire B,     // Input B
    input  wire Sel,   // Select signal
    output wire Out    // Output
);

    assign Out = Sel ? B : A;

endmodule

