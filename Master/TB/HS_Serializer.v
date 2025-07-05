module HS_Serializer (
    input wire TxWordClkHs,            // Slow clock for loading parallel data
    input wire TxSymbolClkHS,          // Fast clock for serializing data
    input wire rst,                 // Reset signal 
    input wire [6:0] TxPolarity,TxRotation,TxFlip,     // Parallel data inputs
    input wire SerializerEn,                           // Serializer enable signal
    output reg [2:0] SerSym                            // Serialized output
);

reg[2:0] counter=0;                        // Counter for the number of symbols serialized
reg load ;                              // Load signal to indicate when to load new data into the serializer


always@(posedge TxWordClkHs or negedge rst) begin
    if (!rst) begin
        load <= 0;
    end
    else if (SerializerEn) begin
        load <= 1;
    end
   else begin
        load <= 0;
    end
end

always@(negedge TxSymbolClkHS or negedge rst ) begin
    if (!rst) begin
        SerSym <= 3'b000;
    end
    else if (load) begin
                 if (counter < 'd7) begin
                       SerSym <= {TxFlip[counter],TxRotation[counter],TxPolarity[counter]};
                       counter <= counter + 1;
                end
                 else begin
                       counter <= 0;
                 end
    end
        else begin
               counter <= 0; // Reset counter signal after all bits are serialized 
                end

    
    end

endmodule