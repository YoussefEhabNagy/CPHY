module Clock_Recovery_HS (
    input A,
    input B,
    input C,
    input RST,
    output RecoveredClk
);

    wire SlowClk;
    

    Pulse_Generation PulseGen (
    .A(A),
    .B(B),
    .C(C),
    .OutClk(SlowClk)
    );

    Clock_Multiplier ClockGen (
    .ClkIn(SlowClk),      
    .SymClk(RecoveredClk)  
	);

    

    
endmodule