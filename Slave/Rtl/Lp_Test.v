module Lp_Test (
    input A,
    input B,
    input C,
    input RST,
    input EscDecoderEn,
    input RequestDetection,
    output RxLpdtEsc,
    output RxUlpsEsc,
    output [3:0] RxTriggerEsc,
    output EscBit,  //output data
    output ErrControl, //wrong command
    output ErrSyncEsc, //wrong number of bits
    output ErrEsc,
    output LpFsmStop
);

    wire RxClkEsc;
    

    Clock_Recovery_LP clock (
    .A(A),
    .C(C),
    .RxClkEsc(RxClkEsc)
    );

    Esc_Decoder Decoder(
        .RxClkEsc(RxClkEsc),
        .RST(RST),
        .EscDecoderEn(EscDecoderEn),
        .A(A),
        .B(B),
        .C(C),
        .RequestDetection(RequestDetection),
        .RxLpdtEsc(RxLpdtEsc),
        .RxUlpsEsc(RxUlpsEsc),
        .RxTriggerEsc(RxTriggerEsc),
        .EscBit(EscBit),
        .ErrControl(ErrControl),
        .ErrSyncEsc(ErrSyncEsc),
        .ErrEsc(ErrEsc),
        .LpFsmStop(LpFsmStop)
    );


    
endmodule