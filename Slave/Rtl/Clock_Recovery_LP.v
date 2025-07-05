//=================================================================================================
//  File Name    : Clock_Recovery_LP.v
//  Description  : 
//      This module implements the Low-Power (LP) Clock Recovery logic for the C-PHY receiver.
//      It generates the Escape Mode clock (RxClkEsc) used during LP communication phases.
//
//      The recovered clock is derived by performing an XOR operation on input signals A and C,
//      which represent the edge transitions on the LP lines. The output clock is gated by the
//      enable signal (En), allowing clock recovery to be active only during appropriate LP phases.
//
//  Key Inputs    : 
//      - En                  : Enable signal for LP clock recovery
//      - A, C                : LP line signals used to recover the escape clock
//
//  Key Outputs   : 
//      - RxClkEsc            : Recovered clock for LP Escape Mode
//
//  Author       : Amira
//  Date         : 18/5/2025
//=================================================================================================

module Clock_Recovery_LP (
    input A,
    input C,
    output RxClkEsc
    );

    assign RxClkEsc = A^C ;

endmodule