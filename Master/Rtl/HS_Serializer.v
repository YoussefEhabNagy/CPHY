module HS_Serializer (
    input wire TxSymbolClkHS,          // Fast clock for serializing data
    input wire RstN,                 // Reset signal 
    input wire [6:0] TxPolarity,TxRotation,TxFlip,     // Parallel data inputs
    input wire HsSerializerEn,                           // Serializer enable signal
    output reg [2:0] SerSym                            // Serialized output
);

reg[2:0] counter;                        // Counter for the number of symbols serialized
reg [6:0] TxPolarity_reg,TxRotation_reg,TxFlip_reg; // Data registers  to hold the parallel data to make pripheral change data without changing the data in the serializer

always@(negedge TxSymbolClkHS or negedge RstN ) begin
    if (!RstN) begin
        SerSym <= 3'b000;
        counter <= 0;
        TxPolarity_reg <= 0;
        TxRotation_reg <= 0;
        TxFlip_reg <= 0;
    end
    else if (HsSerializerEn) begin
        if (counter == 0) begin                                     // Load the parallel data into registers and output the first bit immediately
            TxPolarity_reg <= TxPolarity;
            TxRotation_reg <= TxRotation;
            TxFlip_reg <= TxFlip;
            SerSym <= {TxFlip[counter],TxRotation[counter],TxPolarity[counter]};
            counter <= 1;
            end
        else if (counter == 3'd6) begin
            TxPolarity_reg <= TxPolarity_reg;
            TxRotation_reg <= TxRotation_reg;
            TxFlip_reg <= TxFlip_reg;
            SerSym <= {TxFlip_reg[counter],TxRotation_reg[counter],TxPolarity_reg[counter]};
            counter <= 0;    // Reset counter signal after all bits are serialized
        end
        else begin               // Output the next bit
            TxPolarity_reg <= TxPolarity_reg;
            TxRotation_reg <= TxRotation_reg;
            TxFlip_reg <= TxFlip_reg;
            SerSym <= {TxFlip_reg[counter],TxRotation_reg[counter],TxPolarity_reg[counter]};
            counter <= counter + 1;
        end
    end
    else begin
        counter <= 0; // Reset counter signal if serializer is disabled
        SerSym <= 3'b000;
        TxPolarity_reg <= 0;
        TxRotation_reg <= 0;
        TxFlip_reg <= 0;
    end

end

endmodule