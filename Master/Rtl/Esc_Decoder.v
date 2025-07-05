
`timescale 1ns / 1ps

module Esc_Decoder (
    input RxClkEsc,
    input RST,
    input EscDecoderEn,
    input A,
    input B,
    input C,
    input RequestDetection,
    output reg RxLpdtEsc,
    output reg RxUlpsEsc,
    output reg [3:0] RxTriggerEsc,
    output reg EscBit,  //output data
    output reg ErrEsc, //wrong command
    output reg ErrSyncEsc, //wrong number of bits
    output reg ErrControl,  // incorrect line state sequence is detected
    output reg LpFsmStop,
    output reg EscDeserEn
    );

    localparam idle = 2'b00;
    localparam CommandRead = 2'b01; //Reading command
    localparam LpdtData = 2'b11; //Read Low power data
    localparam LpdtCommand = 8'b11100001; //Low power data transmission command
    localparam UlpsCommand = 8'b00011110; //Ultra Low power command
    localparam ResetTrigger = 8'b01100010; //Reset Trigger command

    reg [1:0] CurrentState, NextState; 
    reg [7:0] Command;
    reg [2:0] Counter;
    reg RxLpdtEsc_reg;
    reg RxUlpsEsc_reg;
    reg [3:0] RxTriggerEsc_reg;
    reg ErrEsc_reg;
    wire clk;
    wire is_stop;

    `ifdef SYNTHESIS
    // Synthesis directives to prevent simulation-only code from being synthesized
    assign  clk = RxClkEsc; 

    `else
    // Simulation-only code
    assign #(1) clk = RxClkEsc; //For simulation as the data and clk change at the same time
    `endif
    assign is_stop = (A && B && C);
    

    always @(posedge clk or negedge RST) begin
        if (!RST) begin
            CurrentState <= idle;    
        end else begin   
            CurrentState <= NextState; 
        end
    end

    always @(posedge clk or negedge RST) begin
        if (!RST) begin  
            Counter <= 3'b0;
            Command <= 8'b0;
            EscBit <= 1'b0;
            EscDeserEn <= 1'b0;
        end else begin   
            if(NextState == CommandRead ) begin
                Counter <= Counter + 1;
                Command <= {Command[6:0], A};
                EscBit <= 1'b0;
                EscDeserEn <= 1'b0;
            end   
            else if (NextState == LpdtData) begin
                Counter <= Counter + 1;
                EscBit <= A;
                EscDeserEn <= 1'b1;
                Command <= 8'b0;
            end
            else begin
                Counter <= 3'b0;
                Command <= 8'b0;
                EscBit <= 1'b0;
                EscDeserEn <= 1'b0;
            end    
        end
    end

   always @(negedge clk or negedge RST) begin
	 if (!RST) begin
		RxTriggerEsc <= 4'b0;
		RxUlpsEsc <= 1'b0;
		RxLpdtEsc <= 1'b0;
		ErrEsc <= 1'b0;
	end
	else if (is_stop) begin
        RxTriggerEsc <= 4'b0;
		RxUlpsEsc <= 1'b0;
		RxLpdtEsc <= 1'b0;
		ErrEsc <= 1'b0;
    end 
	else begin
		RxTriggerEsc <= RxTriggerEsc_reg;
		RxUlpsEsc <= RxUlpsEsc_reg;
		RxLpdtEsc <= RxLpdtEsc_reg;
		ErrEsc <= ErrEsc_reg;
	end


  end

    //Assign next state 
    always @(*) begin
        case (CurrentState)
            idle : begin
                if(EscDecoderEn) begin
                    NextState = CommandRead;
                end
                else begin
                    NextState = idle;
                end
            end

            CommandRead : begin
                if (EscDecoderEn) begin
                    if (Counter == 3'd0) begin 
			if(RxLpdtEsc_reg) begin
                        	NextState = LpdtData;
			end
			else begin
				NextState = idle;	
			end 
                    end
                    else begin
                        NextState = CommandRead;
                    end
                end
                else begin
                    NextState = idle;
                end
            end

            LpdtData : begin
                if(EscDecoderEn) begin
                    if (is_stop) begin
                        NextState = idle;    
                    end
                    else if (EscDecoderEn) begin
                        NextState = LpdtData; 
                    end 
                    else
                    begin
                        NextState = idle;    
                    end
                end
                else begin
                    NextState = idle;    
                end
            end

            default: begin
                NextState = idle;
            end 
        endcase
        
    end

    //Assign output 
    always @(*) begin
        case (CurrentState)
            idle: begin
                RxLpdtEsc_reg = 1'b0;
                RxUlpsEsc_reg = 1'b0;
                RxTriggerEsc_reg = 4'b0;
                ErrEsc_reg = 1'b0;   
            end
            CommandRead : begin
                if (Counter == 3'd0) begin 
                if (Command == LpdtCommand) begin
                        RxLpdtEsc_reg = 1'b1;
                        RxUlpsEsc_reg = 1'b0;
                        RxTriggerEsc_reg = 4'b0; 
                        ErrEsc_reg = 1'b0;
                    end
                    else if (Command == UlpsCommand) begin
                        RxUlpsEsc_reg = 1'b1;
                        RxLpdtEsc_reg = 1'b0;
                        RxTriggerEsc_reg = 4'b0;
                        ErrEsc_reg = 1'b0; 
                    end
                    else if (Command == ResetTrigger) begin
                        RxTriggerEsc_reg = 4'b1;
                        RxUlpsEsc_reg = 1'b0;
                        RxLpdtEsc_reg = 1'b0;
                        ErrEsc_reg = 1'b0;
                    end
                    else begin
                        RxLpdtEsc_reg = 1'b0;
                        RxUlpsEsc_reg = 1'b0;
                        RxTriggerEsc_reg = 4'b0;
                        ErrEsc_reg = 1'b1;
                    end 
                end
                else begin
                    RxLpdtEsc_reg = 1'b0;
                    RxUlpsEsc_reg = 1'b0;
                    RxTriggerEsc_reg = 4'b0;
                    ErrEsc_reg = 1'b0;
                end
            end
            LpdtData : begin
                RxUlpsEsc_reg = 1'b0;
                RxTriggerEsc_reg = 4'b0;
                RxLpdtEsc_reg = 1'b1;
                ErrEsc_reg = 1'b0;
            end
            default: begin
                RxLpdtEsc_reg = 1'b0;
                RxUlpsEsc_reg = 1'b0;
                RxTriggerEsc_reg = 4'b0;
                ErrEsc_reg = 1'b0;
            end 
        endcase
    end

    //check the no. of input bits at the end of the receiving data
    always @(*) begin
        if(is_stop) begin
            if (EscDecoderEn) begin
                LpFsmStop = 1'b1;
                if (Counter == 1)
                begin
                    ErrSyncEsc = 1'b0;    
                end
                else begin
                    ErrSyncEsc = 1'b1;     
                end
            end
            else begin
               ErrSyncEsc = 1'b0; 
               LpFsmStop = 1'b0; 
            end
        end 
        else begin
            ErrSyncEsc = 1'b0; 
            LpFsmStop = 1'b0; 
        end 
    end

    //check  incorrect line state sequence while control (111 instead of bridge)
    always @(*) begin
        if(is_stop) begin
            if (RequestDetection) begin
                ErrControl = 1'b1;
            end
            else begin
                ErrControl = 1'b0;
            end
        end
        else begin
            ErrControl = 1'b0;
        end
    end
    
endmodule