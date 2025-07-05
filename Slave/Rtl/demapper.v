//<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=
//  File Name    : demapper.v
//  Description  : 
//      This module implements the demapping logic for the C-PHY receiver.
//      It decodes the 7-bit RxFlip pattern to determine the appropriate bit selection (muxing) 
//      for each symbol from the RxPolarity and RxRotation inputs. Based on this mapping,
//      it assembles a 16-bit parallel data word (RxDataHS).
//
//      The module also flags any invalid RxFlip patterns using RxInvalidCodeHS.
//
//  Key Inputs    : 
//      - RxFlip              : 7-bit vector indicating the flip value of each received symbol
//      - RxRotation          : 7-bit rotation vector
//      - RxPolarity          : 7-bit polarity vector
//
//  Key Outputs   : 
//      - RxDataHS            : 16-bit parallel high-speed output data
//      - RxInvalidCodeHS     : Error flag indicating invalid RxFlip code
//
//  Author       : Ahmed
//  Date         : 19/5/2025
//<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=<=


module demapper (
    input wire clk,
    input wire rst_n,
    input wire [6:0] RxFlip,
    input wire [6:0] RxRotation,
    input wire [6:0] RxPolarity,
    output reg [15:0] RxDataHS,
    output reg  RxInvalidCodeHS
);
///////////////////CODE REVIEW/////////////////
/// It's preferred to separate always blocks for outputs.
/// It's preferred to use localparam for Readability. 
////////////////////////////////////////////////
wire muxa0,muxa1,muxa2,muxa3,muxa4,muxa5,muxb0,muxb1,muxb2,muxb3,muxb4,muxb5,mux6;
reg [12:0] mux_values;
reg temp_invalidcode_stage1,temp_invalidcode_stage2;
assign {mux6,muxb5,muxa5,muxb4,muxa4,muxb3,muxa3,muxb2,muxa2,muxb1,muxa1,muxb0,muxa0}=mux_values;
reg most_zero;
reg most_one;
reg most_two;
reg most_three;
reg most_four;
reg most_five;

reg [5:0] temp_signal;


///// pipeline the case statment for RxFlip[6:4] to avoid setup time violations /////

always@(posedge clk or negedge rst_n)
    begin
        if (!rst_n) begin
            most_zero <= 1'b0;
            most_one <= 1'b0;
            most_two <= 1'b0;
            most_three <= 1'b0;
            most_four <= 1'b0;
            most_five <= 1'b0;
            temp_invalidcode_stage1 <= 1'b0;
        end
    else
    begin    
        case(RxFlip[6:4])                /////check the 3 MSB of RxFlip
        'h0:begin
            most_zero <= 1'b1;
            most_four <= 1'b0;
            most_three <= 1'b0;
            most_two <= 1'b0;
            most_one <= 1'b0;
            temp_invalidcode_stage1 <= 1'b0;

        end
        'h1:begin
            most_zero <= 1'b0;
            most_one <= 1'b1;
            most_two <= 1'b0;
            most_three <= 1'b0;
            most_four <= 1'b0;
            temp_invalidcode_stage1 <= 1'b0;
        end
        'h2:begin
            most_zero <= 1'b0;
            most_one <= 1'b0;
            most_two <= 1'b1;
            most_three <= 1'b0;
            most_four <= 1'b0;
            most_five <= 1'b0;
            temp_invalidcode_stage1 <= 1'b0;
        end
        'h3:begin
            most_zero <= 1'b0;
            most_one <= 1'b0;
            most_two <= 1'b0;
            most_three <= 1'b1;
            most_four <= 1'b0;
            most_five <= 1'b0;
            temp_invalidcode_stage1 <= 1'b0;
        end
        'h4:begin
            most_zero <= 1'b0;
            most_one <= 1'b0;
            most_two <= 1'b0;
            most_three <= 1'b0;
            most_four <= 1'b1;
            most_five <= 1'b0;
            temp_invalidcode_stage1 <= 1'b0;
        end
        'h5:begin
            most_zero <= 1'b0;
            most_one <= 1'b0;
            most_two <= 1'b0;
            most_three <= 1'b0;
            most_four <= 1'b0;
            most_five <= 1'b1;
            temp_invalidcode_stage1 <= 1'b0;
        end
        default: begin
            most_zero <= 1'b0;
            most_one <= 1'b0;
            most_two <= 1'b0;
            most_three <= 1'b0;
            most_four <= 1'b0;
            most_five <= 1'b0;
            temp_invalidcode_stage1 <= 1'b1; // Set invalid code flag
        end
        endcase
    end
    end
always@(posedge clk or negedge rst_n)
    begin
        if (!rst_n) begin
            temp_signal <= 6'b0;
             temp_invalidcode_stage2 <= 1'b0;
             mux_values <= 13'b0;
        end
    else
    begin    
                    ///check the least 4 bit and put the data in temp signal//////////
        if(&most_zero)begin
            case(RxFlip[3:0])                /////check the 4 LSB of RxFlip
            4'h0: begin                                                              //0x00
                mux_values <= 13'b0_00_00_00_00_00_00;
                temp_signal[1:0] <= 2'b0;       //// don't care XXXXXX
                temp_signal[3:2] <= 2'b0;
                temp_signal[5:4] <= 2'h0;
                temp_invalidcode_stage2 <=temp_invalidcode_stage1 ;  
            end
            4'h1: begin                                                             //0x01              
                mux_values <= 13'b1_01_01_01_01_01_01;
                temp_signal[1:0] <= 2'b0;
                temp_signal[3:2] <= 2'b0;
                temp_signal[5:4] <= 2'h1;
                temp_invalidcode_stage2 <=temp_invalidcode_stage1 ;  
            end
            4'h2: begin                                                              //0x02
                mux_values <= 13'b1_01_01_01_01_01_00;
                temp_signal[1:0] <= 2'h0;
                temp_signal[3:2] <= 2'h1;
                temp_signal[5:4] <= 2'h1;
                temp_invalidcode_stage2 <=temp_invalidcode_stage1 ;  
            end 
            4'h4: begin                                                               //0x04                                            
                mux_values <= 13'b1_01_01_01_01_00_00;
                temp_signal[1:0] <= 2'h0;
                temp_signal[3:2] <= 2'h2;
                temp_signal[5:4] <= 2'h1;
                temp_invalidcode_stage2 <=temp_invalidcode_stage1 ;  
            end
            4'h8: begin                                                               //0x08                
                mux_values <= 13'b1_01_01_01_00_00_00;
                temp_signal[1:0] <= 2'h0;
                temp_signal[3:2] <= 2'h3;
                temp_signal[5:4] <= 2'h1;
                temp_invalidcode_stage2 <=temp_invalidcode_stage1 ;  
            end
            4'h3: begin                                                           //0x03                                    
                mux_values <= 13'b1_10_10_10_10_10_10;
                temp_signal[1:0] <= 2'h0;
                temp_signal[3:2] <= 2'h3;
                temp_signal[5:4] <= 2'h2;
                temp_invalidcode_stage2 <=temp_invalidcode_stage1 ;  
            end
            4'h5: begin                                                       //0x05                
                mux_values <= 13'b1_10_10_10_10_10_01;
                temp_signal[1:0] <= 2'h1;
                temp_signal[3:2] <= 2'h3;
                temp_signal[5:4] <= 2'h2;
                temp_invalidcode_stage2 <=temp_invalidcode_stage1 ;  
            end
            4'h9: begin                                                            //0x09          
                mux_values <= 13'b1_10_10_10_10_01_01;
                temp_signal[1:0] <= 2'h2;
                temp_signal[3:2] <= 2'h3;
                temp_signal[5:4] <= 2'h2;
                temp_invalidcode_stage2 <=temp_invalidcode_stage1 ;  
            end
            4'h6: begin                                                           //0x06                            
                mux_values <= 13'b1_10_10_10_10_10_00;
                temp_signal[1:0] <= 2'h2;
                temp_signal[3:2] <= 2'h0;
                temp_signal[5:4] <= 2'h3;
                temp_invalidcode_stage2 <=temp_invalidcode_stage1 ;  
            end
            4'ha: begin                                                           //0x0A                        
                mux_values <= 13'b1_10_10_10_10_01_00;
                temp_signal[1:0] <= 2'h3;
                temp_signal[3:2] <= 2'h0;
                temp_signal[5:4] <= 2'h3;
                temp_invalidcode_stage2 <=temp_invalidcode_stage1 ;  
            end
            4'hc: begin                                                          //0x0C         
                mux_values <= 13'b1_10_10_10_10_00_00;
                temp_signal[1:0] <= 2'h3;
                temp_signal[3:2] <= 2'h1;
                temp_signal[5:4] <= 2'h3;
                temp_invalidcode_stage2 <=temp_invalidcode_stage1 ;  
            end
            default: begin
                mux_values <= 13'b1_00_00_00_00_00_00;
                temp_signal[1:0] <= 2'h0;
                temp_signal[3:2] <= 2'h0;
                temp_signal[5:4] <= 2'h0;
                temp_invalidcode_stage2 <= 1'b1; // Set invalid code flag
            end
            endcase
        end
        else if (&most_one) begin
            case(RxFlip[3:0])                /////check the 4 LSB of RxFlip
            4'h0: begin                                                              //0x10
                mux_values <= 13'b1_01_01_00_00_00_00;
                temp_signal[1:0] <= 2'h0;
                temp_signal[3:2] <= 2'h0;
                temp_signal[5:4] <= 2'h2;
                temp_invalidcode_stage2 <=temp_invalidcode_stage1 ;  
  
            end
            4'h1: begin                                                             //0x11              
                mux_values <= 13'b1_10_10_10_01_01_01;
                temp_signal[1:0] <= 2'h3;
                temp_signal[3:2] <= 2'h3;
                temp_signal[5:4] <= 2'h2;
                temp_invalidcode_stage2 <=temp_invalidcode_stage1 ;  
            end 
            4'h2: begin                                                             //0x12
                mux_values <= 13'b1_10_10_10_01_01_00; 
                temp_signal[1:0] <= 2'h0;
                temp_signal[3:2] <= 2'h1;
                temp_signal[5:4] <= 2'h3;
                temp_invalidcode_stage2 <=temp_invalidcode_stage1 ;  
            end
            4'h4: begin                                                         //0x14 
            mux_values <= 13'b1_10_10_10_01_00_00;
            temp_signal[1:0] <= 2'h0;
            temp_signal[3:2] <= 2'h2;
            temp_signal[5:4] <= 2'h3;
            temp_invalidcode_stage2 <=temp_invalidcode_stage1 ;  
        end

            4'h8: begin                                                               //0x18                
            mux_values <= 13'b1_10_10_10_00_00_00;
            temp_signal[1:0] <= 2'h3;
            temp_signal[3:2] <= 2'h2;
            temp_signal[5:4] <= 2'h3;
            temp_invalidcode_stage2 <=temp_invalidcode_stage1 ;  
            end
            default: begin
                mux_values <= 13'b1_00_00_00_00_00_00;
                temp_signal[1:0] <= 2'h0;
                temp_signal[3:2] <= 2'h0;
                temp_signal[5:4] <= 2'h0;
                temp_invalidcode_stage2 <= 1'b1; // Set invalid code flag
            end
            endcase
        end
        else if (&most_two)
        begin
            case(RxFlip[3:0])                /////check the 4 LSB of RxFlip
            4'h0: begin                                                              //0x20
                mux_values <= 13'b1_01_00_00_00_00_00;
                temp_signal[1:0] <= 2'h0;
                temp_signal[3:2] <= 2'h1;
                temp_signal[5:4] <= 2'h2;
                temp_invalidcode_stage2 <=temp_invalidcode_stage1 ;  
            end
            4'h1: begin                                                             //0x21              
                mux_values <= 13'b1_10_10_01_01_01_01;
                temp_signal[1:0] <= 2'h0;
                temp_signal[3:2] <= 2'h0;
                temp_signal[5:4] <= 2'h3;
                temp_invalidcode_stage2 <=temp_invalidcode_stage1 ;  
            end 
            4'h2: begin                                                              //0x22
                mux_values <= 13'b1_10_10_01_01_01_00;
                temp_signal[1:0] <= 2'h1;
                temp_signal[3:2] <= 2'h1;
                temp_signal[5:4] <= 2'h3;
                temp_invalidcode_stage2 <= temp_invalidcode_stage1;
            end
            4'h4: begin                                                               //0x24                                            
                mux_values <= 13'b1_10_10_01_01_00_00;
                temp_signal[1:0] <= 2'h1;
                temp_signal[3:2] <= 2'h2;
                temp_signal[5:4] <= 2'h3;
                temp_invalidcode_stage2 <=temp_invalidcode_stage1 ;  
            end
            4'h8: begin                                                               //0x28                
                mux_values <= 13'b1_10_10_01_00_00_00;
                temp_signal[1:0] <= 2'h0;
                temp_signal[3:2] <= 2'h3;
                temp_signal[5:4] <= 2'h3;
                temp_invalidcode_stage2 <=temp_invalidcode_stage1 ;  
            end
            default: begin
                mux_values <= 13'b1_00_00_00_00_00_00;
                temp_signal[1:0] <= 2'h0;
                temp_signal[3:2] <= 2'h0;
                temp_signal[5:4] <= 2'h0;
                temp_invalidcode_stage2 <= 1'b1; // Set invalid code flag
            end
        endcase
        end
        else if (&most_three)                                               //0x30
        begin                                                             
                mux_values <= 13'b1_10_10_00_00_00_00;
                temp_signal[1:0] <= 2'h2;
                temp_signal[3:2] <= 2'h3;
                temp_signal[5:4] <= 2'h3;
                temp_invalidcode_stage2 <=temp_invalidcode_stage1 ;  
        end
        else if (&most_four)
        begin
            case(RxFlip[3:0])                /////check the 4 LSB of RxFlip
            4'h0: begin                                                              //0x40
                mux_values <= 13'b1_00_00_00_00_00_00;
                temp_signal[1:0] <= 2'h0;
                temp_signal[3:2] <= 2'h2;
                temp_signal[5:4] <= 2'h2;
                temp_invalidcode_stage2 <=temp_invalidcode_stage1 ;  
            end
            4'h1: begin                                                             //0x41              
                mux_values <= 13'b1_10_01_01_01_01_01;
                temp_signal[1:0] <= 2'h1;
                temp_signal[3:2] <= 2'h0;
                temp_signal[5:4] <= 2'h3;
                temp_invalidcode_stage2 <=temp_invalidcode_stage1 ;  
            end
            4'h2: begin                                                              //0x42
                mux_values <= 13'b1_10_01_01_01_01_00;
                temp_signal[1:0] <= 2'h2;
                temp_signal[3:2] <= 2'h1;
                temp_signal[5:4] <= 2'h3;
                temp_invalidcode_stage2 <=temp_invalidcode_stage1 ;  
            end
            4'h4: begin                                                               //0x44                                            
                mux_values <= 13'b1_10_01_01_00_00_00;
                temp_signal[1:0] <= 2'h2;
                temp_signal[3:2] <= 2'h2;
                temp_signal[5:4] <= 2'h3;
                temp_invalidcode_stage2 <=temp_invalidcode_stage1 ;  
            end
            4'h8: begin                                                               //0x48                
                mux_values <= 13'b1_10_01_00_00_00_00;
                temp_signal[1:0] <= 2'h1;
                temp_signal[3:2] <= 2'h3;
                temp_signal[5:4] <= 2'h3;
                temp_invalidcode_stage2 <=temp_invalidcode_stage1 ;  
            end
            default: begin
                mux_values <= 13'b1_00_00_00_00_00_00;
                temp_signal[1:0] <= 2'h0;
                temp_signal[3:2] <= 2'h0;
                temp_signal[5:4] <= 2'h0;
                temp_invalidcode_stage2 <= 1'b1; // Set invalid code flag
            end
            endcase
        end
        else if (&most_five) begin                                                           //0x50
                mux_values <= 13'b1_10_01_00_00_00_00;
                temp_signal[1:0] <= 2'h3;
                temp_signal[3:2] <= 2'h3;
                temp_signal[5:4] <= 2'h3;
                temp_invalidcode_stage2 <= 1'b0; // Default value for invalid code
            end
        else begin
            mux_values <= 13'b1_00_00_00_00_00_00;
            temp_signal[1:0] <= 2'h0;
            temp_signal[3:2] <= 2'h0;
            temp_signal[5:4] <= 2'h0;
            temp_invalidcode_stage2 <= 1'b1; // Set invalid code flag
        end
    end
    end
    


always@(posedge clk or negedge rst_n)
    begin
        if (!rst_n) begin
            RxDataHS <= 16'b0;
            RxInvalidCodeHS <= 1'b0;
        end
    
    else begin
    RxInvalidCodeHS <= temp_invalidcode_stage2; // Assign the invalid code flag to output
    
    case ({muxb0,muxa0})                  ////first mux
        2'b00: begin
            RxDataHS[0] <= RxPolarity[0];
            RxDataHS[1] <= RxRotation[0];
        end
        2'b01: begin
            RxDataHS[0] <= RxPolarity[1];
            RxDataHS[1] <= RxRotation[1];
        end
        2'b10: begin
            RxDataHS[0] <= RxPolarity[2];
            RxDataHS[1] <= RxRotation[2];
        end
        default: begin
            RxDataHS[0] <= 1'b0;
            RxDataHS[1] <= 1'b0;
        end
    endcase
    case ({muxb1,muxa1})                  ////second mux
        2'b00: begin
            RxDataHS[2] <= RxPolarity[1];
            RxDataHS[3] <= RxRotation[1];
        end
        2'b01: begin
            RxDataHS[2] <= RxPolarity[2];
            RxDataHS[3] <= RxRotation[2];
        end
        2'b10: begin
            RxDataHS[2] <= RxPolarity[3];
            RxDataHS[3] <= RxRotation[3];
        end
        default: begin
            RxDataHS[2] <= 1'b0;
            RxDataHS[3] <= 1'b0;
        end
    endcase
    case ({muxb2,muxa2})                  ////third mux
        2'b00: begin
            RxDataHS[4] <= RxPolarity[2];
            RxDataHS[5] <= RxRotation[2];
        end
        2'b01: begin
            RxDataHS[4] <= RxPolarity[3];
            RxDataHS[5] <= RxRotation[3];
        end
        2'b10: begin
            RxDataHS[4] <= RxPolarity[4];
            RxDataHS[5] <= RxRotation[4];
        end
        default: begin
            RxDataHS[4] <= 1'b0;
            RxDataHS[5] <= 1'b0;
        end
    endcase
    case ({muxb3,muxa3})                  ////fourth mux
        2'b00: begin
            RxDataHS[6] <= RxPolarity[3];
            RxDataHS[7] <= RxRotation[3];
        end
        2'b01: begin
            RxDataHS[6] <= RxPolarity[4];
            RxDataHS[7] <= RxRotation[4];
        end
        2'b10: begin
            RxDataHS[6] <= RxPolarity[5];
            RxDataHS[7] <= RxRotation[5];
        end
        default: begin
            RxDataHS[6] <= 1'b0;
            RxDataHS[7] <= 1'b0;
        end
    endcase
    case ({muxb4,muxa4})                  ////fifth mux
        2'b00: begin
            RxDataHS[8] <= RxPolarity[4];
            RxDataHS[9] <= RxRotation[4];
        end
        2'b01: begin
            RxDataHS[8] <= RxPolarity[5];
            RxDataHS[9] <= RxRotation[5];
        end
        2'b10: begin
            RxDataHS[8] <= RxPolarity[6];
            RxDataHS[9] <= RxRotation[6];
        end
        default: begin
            RxDataHS[8] <= 1'b0;
            RxDataHS[9] <= 1'b0;
        end
    endcase
    case ({muxb5,muxa5})                  ////sixth mux
        2'b00: begin
            RxDataHS[10] <= RxPolarity[5];
            RxDataHS[11] <= RxRotation[5];
        end
        2'b01: begin
            RxDataHS[10] <= RxPolarity[6];
            RxDataHS[11] <= RxRotation[6];
        end
        2'b10: begin
            RxDataHS[10] <= temp_signal[0];
            RxDataHS[11] <= temp_signal[1];
        end
        default: begin
            RxDataHS[10] <= 1'b0;
            RxDataHS[11] <= 1'b0;
        end
    endcase
    if (!mux6) begin
        RxDataHS[12] <= RxPolarity[6];
        RxDataHS[13] <= RxRotation[6];
    end else begin
        RxDataHS[12] <= temp_signal[2];
        RxDataHS[13] <= temp_signal[3];
    end
    RxDataHS[14] <= temp_signal[4];
    RxDataHS[15] <= temp_signal[5];
    end
    end
    endmodule
