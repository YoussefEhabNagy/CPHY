//=================================================================================================
//  File Name    : Sequence_Detector.v
//  Description  : 
//      Implements a finite state machine (FSM) to detect critical sequences in a C-PHY high-speed
//      receiver path. Identifies PREAMBLE, SYNC, POST, and DATA sequences from 3-bit symbol streams,
//      while monitoring Start-Of-Transmission (SOT) protocol violations. Designed for integration
//      with HS deserialization logic in C-PHY receivers.
//
//      Key Features:
//      - Detects 4 sequence types via one-hot encoded output
//      - Symbol-count tracking for sequence validation
//      - SOT error detection (sync mismatches, invalid transitions)
//      - Clock-domain aligned with HS symbol rate
//
//  Key Inputs   :
//      - RxSymClkHS         : High-speed symbol clock (aligned with symbol rate)
//      - RxSymbol [2:0]     : 3-bit decoded symbol input (HS lane)
//      - HsSeqDetectorEn    : Global enable (always active in current implementation)
//
//  Key Outputs  :
//      - DetectedSeq [3:0]  : One-hot flags:
//                             [0] PREAMBLE, [1] SYNC, [2] POST, [3] DATA
//      - ErrSotHS           : SOT protocol violation
//      - ErrSotSyncHs       : SYNC sequence alignment error
//
//  FSM Operation:
//      - IDLE       : Awaits initial symbol (3'h3 or 3'h4)
//      - PRE_SYNC   : Potential preamble/sync transition state
//      - SYNC_POST  : SYNC/POST differentiation state
//      - PREAMBLE   : Validates 8-symbol preamble sequence
//      - SYNC       : Verifies 6-symbol sync pattern
//      - POST       : Detects post-amble sequence
//
//  Error Handling:
//      - Triggers ErrSotSyncHs on SYNC symbol count mismatch
//      - Asserts ErrSotHS for invalid sequence transitions
//      - Auto-reset to IDLE on errors
//
//  Design Notes:
//      - Symbol counter (symbol_count) enforces sequence length constraints
//      - PREAMBLE detection requires minimum 8 consecutive 3'h3 symbols
//      - Implicit DATA state detection when no control sequences active
//
//  Author       : Mohamed Emam
//  Date         : 24/05/2025
//=================================================================================================
`timescale 1ns / 1ps
module Sequence_Detector (
    input        	 RxSymClkHS,
    input        	 RstN,
    input        	 HsSeqDetectorEn,
    input      [2:0] RxSymbol,
    output reg [3:0] DetectedSeq, 
    output reg       ErrSotSyncHs,
    output reg       ErrSotHS
);

    reg [2:0] state;
    reg [2:0] next_state;
    reg [3:0] symbol_count;
    reg [3:0] next_symbol_count;  // Added next symbol count
    
    reg  test_saved_three;
    reg [2:0] saved_three;
    reg [2:0] saved_four;
    reg [3:0] saved_five;
    reg [3:0] saved_six;
	

    localparam PREAMBLE_SEQ = 4'b0001;
    localparam SYNC_SEQ     = 4'b0010;
    localparam POST_SEQ     = 4'b0100;
    localparam DATA_SEQ     = 4'b1000;

    // State encoding
    localparam IDLE      = 3'd0;
    localparam PRE_SYNC  = 3'd1;
    localparam SYNC_POST = 3'd2;
    localparam PREAMBLE  = 3'd3;
    localparam SYNC      = 3'd4;
    localparam POST      = 3'd5;
    localparam DATA      = 3'd6;

    // Sequential logic for state and counter
    always @(posedge RxSymClkHS or negedge RstN) begin
        if (!RstN) begin
            state         <= IDLE;
            symbol_count  <= 4'd0;
            
            saved_three   <= 3'd3;
            saved_four    <= 3'd4;
            saved_five    <= 3'd5;
            saved_six     <= 4'd6;
        end else
		if(HsSeqDetectorEn)
		begin
            state        <= next_state;
            symbol_count <= next_symbol_count;  // Update counter
            saved_three   <= 3'd3;
            saved_four    <= 3'd4;
            saved_five    <= 3'd5;
            saved_six     <= 4'd6;
        end
    end
    
    // Combinational next state and output logic
    always @(*) begin
        // Default outputs and next values
        next_symbol_count = 1'b0;
        DetectedSeq = 4'b0000;
        ErrSotHS = 1'b0;
        ErrSotSyncHs = 1'b0;   
        case (state)
            IDLE: begin
                if (&(~(RxSymbol ^ saved_three))) begin //using only & operator (and no NOT, XOR, or OR), it's not sufficient to compare equality directly � because & cannot express bit negation or difference by itself.
                    next_state = PRE_SYNC;
                    next_symbol_count = 1; 
                end
                else if (&(~(RxSymbol ^ saved_four))) begin
                    next_state = SYNC_POST;
                    next_symbol_count = 1;  
                end
                else begin
                    next_state = IDLE;
                    next_symbol_count = symbol_count + 1;  
                end
            end
            
            PRE_SYNC: begin
                if (&(~(RxSymbol ^ saved_three))) begin
                    next_state = PREAMBLE;
                    next_symbol_count = symbol_count + 1;
                end
                else if (&(~(RxSymbol ^ saved_four))) begin
                    next_state = SYNC;
                    next_symbol_count = symbol_count + 1;
                end
                else begin
                    next_state = IDLE;
                    next_symbol_count = symbol_count + 1;
                end    
            end
            
            SYNC_POST: begin
                if (&(~(symbol_count ^ saved_five)))
                begin 
                    if (&(~(RxSymbol ^ saved_three)))
                    begin
                        DetectedSeq = SYNC_SEQ;
                        ErrSotHS = 1'b1;
                        next_state = IDLE;
                        next_symbol_count = 4'd0;
                    end
                    else if (&(~(RxSymbol ^ saved_four)))
                    begin
                        next_state = POST;
                        next_symbol_count = symbol_count + 1;
                    end
					else
					begin
						next_state = IDLE;
					end 
                end
                else if ((&(~(RxSymbol ^ saved_four))) || (&(~(RxSymbol ^ saved_three)))) 
                begin
                    next_symbol_count = symbol_count + 1;
                    next_state = SYNC_POST;
                end 
                else 
                begin
                    next_state = IDLE;
                    next_symbol_count = symbol_count + 1;
                end 
            end
            
            PREAMBLE: begin
                if (&(~(RxSymbol ^ saved_three))) begin
                    next_symbol_count = symbol_count + 1;
                    next_state  = PREAMBLE;
                end 
                else if (&(~(RxSymbol ^ saved_four))) begin
                    DetectedSeq = PREAMBLE_SEQ;
                    next_state  = SYNC;
                    next_symbol_count = 4'd1;  // Reset counter for SYNC state
                end
				else
				begin
					DetectedSeq = PREAMBLE_SEQ;
					ErrSotSyncHs = 1'b1;
                    next_state = IDLE;
                    next_symbol_count = 1'b1;
                end
            end

            SYNC: 
            begin
				if ((&(~(RxSymbol ^ saved_three))) && ((&(~(symbol_count ^ saved_six))) || (&(~(symbol_count ^ saved_five))))) begin
					DetectedSeq = SYNC_SEQ;
					next_state = IDLE;
					next_symbol_count = 4'd0;
				end
				else
				if ((&(~(RxSymbol ^ saved_four))) && !(&(~(symbol_count ^ saved_six)))) begin
					next_symbol_count = symbol_count + 1;
					next_state = SYNC;
				end
				else
				begin
				    ErrSotSyncHs = 1;
					next_state = IDLE;
					next_symbol_count = 4'd0;
				end
			
            end

            POST: begin
                if (&(~(RxSymbol ^ saved_four))) begin
                    DetectedSeq = POST_SEQ;
                    next_state = IDLE;
                    next_symbol_count = 4'd0;
                end 
                else begin
                    next_symbol_count = symbol_count + 1;
                    next_state = IDLE;
                end
            end
            default : 
                next_state = IDLE;
        endcase
    end
endmodule
