module Word_Clock_Gen (
    input SymClk,
    input RST,
    output RxWordClkHs 
);
    localparam div_num = 3'd7 ;
    localparam saved_four = 3'd4 ;
	
    reg [2:0] pos_count, neg_count;
	wire [2:0] temp1 ;
    wire [2:0] temp2 ;

    always @(posedge SymClk or negedge RST) 
    begin
        if (!RST) begin
            pos_count <=0;
        end
        else if (pos_count ==div_num-1) begin 
            pos_count <= 0;
        end
        else begin
            pos_count<= pos_count +1;
        end
    end
    
    always @(negedge SymClk or negedge RST)
    begin
        if (!RST) begin
            neg_count <=0;
        end
        else  if (neg_count ==div_num-1) begin
            neg_count <= 0;
        end
        else begin 
            neg_count<= neg_count +1; 
        end
    end
    
	assign temp1 = pos_count-saved_four;
    assign temp2 = neg_count-saved_four;
    assign RxWordClkHs = (!temp1[2] || !temp2[2]); 
endmodule