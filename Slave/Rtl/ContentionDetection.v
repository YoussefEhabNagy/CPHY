module ContentionDetection (
    input LpRxA,
    input LpRxB,
    input LpRxC,
    input LpCdA,
    input LpCdB,
    input LpCdC,
    input LpTxA,
    input LpTxB,
    input LpTxC,
    output ErrContentionP0,
    output ErrContentionP1
);
    reg ErrContentionA0;
    reg ErrContentionA1;
    reg ErrContentionB0;
    reg ErrContentionB1;
    reg ErrContentionC0;
    reg ErrContentionC1;

    assign ErrContentionP0 = (ErrContentionA0 | ErrContentionB0 | ErrContentionC0);
    assign ErrContentionP1 = (ErrContentionA1 | ErrContentionB1 | ErrContentionC1);
    // Kindly note that you are not assigning all the signals (ErrContentionA1,ErrContentionA0,ErrContentionB1,...) in all the conditions.
    // Hence, you are making latches. I would suggest that you initially assign all the signals, else you shall initialize all the signals in all conditions.
    always @(*) begin
        //Default values for all sigals to avoid latches
        ErrContentionA1 = 1'b0; 
        ErrContentionB1 = 1'b0; 
        ErrContentionC1 = 1'b0; 
        ErrContentionA0 = 1'b0; 
        ErrContentionB0 = 1'b0; 
        ErrContentionC0 = 1'b0; 
        
        if (LpTxA) begin
            if (!(LpRxA & LpCdA)) begin
                ErrContentionA1 = 1'b1; 
            end
        end
        if (LpTxB) begin
            if (!(LpRxB & LpCdB)) begin
                ErrContentionB1 = 1'b1; 
            end
        end
        if (LpTxC) begin
            if (!(LpRxC & LpCdC)) begin
                ErrContentionC1 = 1'b1; 
            end
        end

        if (!LpTxA) begin
            if (LpRxA | LpCdA) begin
                ErrContentionA0 = 1'b1; 
            end
        end
        if (!LpTxB) begin
            if (LpRxB | LpCdB) begin
                ErrContentionB0 = 1'b1; 
            end
        end
        if (!LpTxC) begin
            if (LpRxC | LpCdC) begin
                ErrContentionC0 = 1'b1; 
            end
        end
    end

endmodule