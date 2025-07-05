module Mux_3Bit (
    input  wire [2:0] SeqSym,      // 3-bit input from sequence
    input  wire [2:0] SerSym,      // 3-bit input from serializer
    input  wire       SerSeqSel,   // Select line
    output wire [2:0] Sym          // 3-bit output
);

    assign Sym = SerSeqSel ? SerSym  : SeqSym;

endmodule

