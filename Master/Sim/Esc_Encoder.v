module Esc_Encoder (
    input TxClkEsc,
    input RstN,
    input EscBit,
    input EscEncoderEn,
    input DataValid, 
    output reg A,
    output reg B,
    output reg C
);

    reg data_A;
    reg data_C;
	reg Enable1; // Used to control the encoding 
	reg Enable0; // Used to control the encoding 

	// Posedge: sample data 
	always @(posedge TxClkEsc or negedge RstN) begin
		if (!RstN) begin
			data_A <= 0;
			data_C <= 0;
			Enable1 <= 0;
		end else if (EscEncoderEn && DataValid) begin // Data is ready and valid to be sent
			data_A <= EscBit;
			data_C <= ~EscBit;
			Enable1 <= ~Enable1; //Toggle at negedge
		end else if (EscEncoderEn && ~DataValid) begin    // Space send
			data_A <= 1'b0;
			data_C <= 1'b0;
			Enable1 <= ~Enable1; 
		end
		else begin
			data_A <= 1'b0;
			data_C <= 1'b0;
			Enable1 <= 1'b0;
		end
	end

	
	always@(negedge TxClkEsc or negedge RstN) begin
		if(!RstN) begin
			Enable0 <= 1'b0;
		end
		else if (EscEncoderEn) begin
			Enable0 <= ~Enable0; //Toggle at negedge
		end
		else begin
			Enable0 <= 1'b0;
		end
		
	end
	
	always@(*) begin
		if(Enable1^Enable0) begin
			A = data_A;
			B = 1'b0;
			C = data_C;
		end
		else begin
			A = 1'b0;
			B = 1'b0;
			C = 1'b0;
		end
	end
endmodule
