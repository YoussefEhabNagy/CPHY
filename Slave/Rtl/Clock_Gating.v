module Clock_Gating (
    input ClkIn,
    input Enable,
    output SymClk
);

	reg LatchEn;
	
	assign SymClk = ClkIn && LatchEn;
	
    always @(ClkIn or Enable) begin
		if (!ClkIn) begin
			LatchEn <= Enable;
		end
    end 
 
endmodule