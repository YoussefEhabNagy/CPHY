module TX_Ctrl_Logic (
    input wire [1:0] TxCtrlOut,            //  input signal for control logic
    output reg A,B,C                      // Output signals for the control logic
    );



    always @(*) begin
        case (TxCtrlOut)
            2'b00: begin            // Tx _stop state 
                A = 1'b1;
                B = 1'b1;
                C = 1'b1;
            end
            2'b01: begin           // Tx_Esc Request state  &TX_HS request state 
                A = 1'b0;
                B = 1'b0;
                C = 1'b1;
            end
            2'b10: begin           // Lp yield state  &tx Esc Go state  & TX_Ulps state &TA Go state &TX_Hs prepare state
                A = 1'b0;
                B = 1'b0;
                C = 1'b0;
            end
            2'b11: begin           //Lp Request  &turn around request  state
                A = 1'b1;
                B = 1'b0;
                C = 1'b0;
            end
            default: begin
                A = 1'b0;
                B = 1'b0;
                C = 1'b0; // Default case to know if there is an error in the input signal
            end
        endcase
    end
   endmodule