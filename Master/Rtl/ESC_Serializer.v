module ESC_Serializer (
    input  wire       TxClkEsc,                  // Clock for loading and shifting
    input  wire       RstN,                       // Active-low Reset
    input  wire [7:0] TxDataEsc,                 // Parallel data input
    input  wire       EscSerEn,                  // Serializer enable
    input  wire       Pause_Ready,
    output reg        TxReadyEsc,                // Ready signal that indicates that the data is taken and ready to be changed
    output reg        LastBit,                   // last bit flag to disable the serializer
    output reg        SerBit                     // Serialized output bit
);

reg [2:0] counter;                        // Bit counter
reg [0:7] TxDataEsc_reg;                 // Data register
reg       ReadyIntermidiate;

always @(posedge TxClkEsc or negedge RstN) begin
    if (!RstN) begin
        SerBit <= 0;
        counter <= 0;
        TxReadyEsc <= 0;
        LastBit <= 0;
        TxDataEsc_reg <= 0;
    end else begin
        if (EscSerEn) begin
            if (counter == 0) begin
                TxDataEsc_reg <= TxDataEsc;
                SerBit <= TxDataEsc[7];           // Output first bit immediately
                counter <= 1;
                TxReadyEsc <= 1;
                LastBit <= 0;
            end else if (counter == 4) begin
                TxDataEsc_reg <= TxDataEsc_reg;
                SerBit <= TxDataEsc_reg[counter]; // Output next bit
                counter <= counter + 1;
                TxReadyEsc <= 0;
                LastBit <= 1;
            end else begin
                TxDataEsc_reg <= TxDataEsc_reg;
                SerBit <= TxDataEsc_reg[counter]; // Output next bit
                counter <= counter + 1;
                TxReadyEsc <= 0;
                LastBit <= 0;
            end
        end else begin
            TxDataEsc_reg <= TxDataEsc_reg;
            TxReadyEsc <= ReadyIntermidiate;
            SerBit <= 0;
            counter <= 0;
            LastBit <= 0;
        end
    end
end

always @(*) begin
    ReadyIntermidiate = Pause_Ready;
end

endmodule