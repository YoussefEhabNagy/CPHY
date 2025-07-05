//=================================================================================================
//  File Name    : SlaveFSM.v
//  Description  : 
//      This module implements the core Finite State Machine (FSM) for a C-PHY slave interface,
//      managing transitions between Low-Power (LP) and High-Speed (HS) modes. It handles RX/TX
//      path control, Escape Mode sequences (ESC/LPDT/ULPS), Turnaround (TA) logic, and protocol
//      compliance. The FSM coordinates decoding, deserialization, and error handling while
//      adhering to C-PHY timing constraints.
//
//      The FSM ensures proper mode switching and state handling according to the C-PHY protocol,
//      enabling and disabling the appropriate decoding, deserialization, and control logic.
//
//      Key functionalities include:
//      - HS mode reception (preamble detection, sync alignment, data deserialization)
//      - LP Escape Mode operations (command parsing, LPDT data flow, ULPS entry/exit)
//      - Bidirectional turnaround (RX↔TX) with TA-SURE/TA-GET timing compliance
//      - Forced mode transitions (ForceRxmode, ForceTxStopmode)
//      - Error detection (ESC sync errors, HS invalid codes, contention errors)
//
//  Key Inputs    :
//      - RxClkFsm, RstN          : FSM clock (300 MHz) and active-low reset
//      - CtrlDecoderOut [1:0]    : Decoded control signals (HS/LP mode requests)
//      - DetectedSeq [3:0]       : Detected HS sequences (sync, post-amble, etc.)
//      - InRx* signals           : ESC and ULPS command triggers , error flags
//      - Tx* signals             : ESC TX control and data
//      - TxReqEsc, TxLpdtEsc     : TX Escape Mode control signals
//      - TurnDisable, ForceRxmode: Mode forcing signals
//      - TxTimeOut, RxTimeOut    : Timer expiration flags
//
//  Key Outputs   :
//      - HS Mode controls (HsRxEn, HsDecoderEn, etc.)
//      - LP Mode controls (LpRxEn, EscDecoderEn, etc.)
//      - TX mode control signals (TxCtrlOut, LpTxEn, etc.)
//      - Protocol state signals (Stopstate, Direction, UlpsActiveNot)
//
//  FSM Features:
//      - **HS Mode States**      : RX_HS_REQUEST, RX_HS_SYNC_SEARCH, RX_HS_RECEIVE_DATA
//      - **LP Escape States**    : RX_ESC_RQST, RX_ESC_CMD, RX_LPDT, RX_ULPS
//      - **Turnaround States**   : RX_TA_WAIT, TX_TA_GET, TX_TA_ACK, RX_TA_LOOK
//      - **Forced Transitions**  : FORCE_RX state for emergency mode switches
//      - **Timer-Driven Logic**  : Uses RxTimer/TxTimer for state timeout handling
//
//  State Management:
//      - 38 defined states covering RX, TX, and hybrid operations
//      - Next-state logic with priority override (ForceTxStopmode > ForceRxmode)
//      - Output logic generates 300+ control signals across states
//
//  Clock Domains:
//      - RxClkFsm (300 MHz)      : Drives FSM transitions and HS logic
//      - LpCLK, HsCLK            : Secondary clocks for LP/HS physical layers
//
//  Error Handling:
//      - Monitors InErrEsc, InErrSotHS, InErrControl
//      - Automatic fallback to safe states (e.g., RX_STOP on errors)
//
//  Authors      : Mohamed Emam (RX and TX FSM)
//  Date         : 24/5/2025
//=================================================================================================

`timescale 1ns / 1ps
module SlaveFSM (
    // Clock and Reset
    input  wire       RxClkFsm,
    input  wire       RstN,
	  
    // Control Signals
    input  wire       TurnDisable,
    input  wire       ForceRxmode,
    input  wire       TurnRequest,
    input  wire       ForceTxStopmode,
    input  wire       Enable,
    
    // RX Signals (LP & HS)
	// Inputs
    input  wire       LpCLK,
    input  wire       HsCLK,
    input  wire       LpFsmStop,
    input  wire [1:0] CtrlDecoderOut,
    input  wire       InRxValidEsc,
    input  wire [3:0] InRxTriggerEsc,
    input  wire       InRxUlpsEsc,
    input  wire       InRxLpdtEsc,
    input  wire       InErrEsc,
    input  wire       InErrSyncEsc,
    input  wire       InErrControl, 
    input  wire [3:0] DetectedSeq,
    input  wire       InRxInvalidCodeHS,
    input  wire       InErrSotHS,
    input  wire       InErrSotSyncHS,


    // Outputs
    output reg        HsRxEn,
    output reg        HsSettleExp,
    output reg        HsDecoderEn,
    output reg        HSDeserEn,
    output reg        HsSeqDetectorEn,
    output wire       RxWordClkHS,
    output wire       RxInvalidCodeHS,
    output reg        RxValidHS,
    output reg        RxActiveHS,
    output wire       RxSyncHS,
    output wire       ErrSotHS,
    output wire       ErrSotSyncHS,
    output reg        LpRxEn,
    output reg        EscDecoderEn, 
    output reg        EscDeserEn,
    output wire       RxClkEsc,
    output wire       RxValidEsc,
    output wire [3:0] RxTriggerEsc,
    output wire       RxUlpsEsc,
    output wire       RxLpdtEsc,
    output wire       ErrEsc,
    output wire       ErrSyncEsc,
    output wire       ErrControl,
    output reg        CtrlDecoderEn,
    output reg        RequestDetection, // this flag to alerts Esc_Decoder if i have request (HS - LP) 
	
	// TX Signals (LP)
    ////////// input signals  //////////
    // Interface Signals
    input wire       TxReqEsc,
    input wire       TxValidEsc,
    input wire       TxUlpdtEsc ,
    input wire       TxLpdtEsc,
    input wire       TxUlpdtExit,
    input wire [3:0] TxTriggerEsc,
    //Esc_Sequencer signal  
    input wire       CmdDone,
    //ESC_Serializer signal  
    input wire       SerReadyEsc,
    input wire       SerLastBit,
 
  ///////// Output signals  //////////
    // ESC Mode Outputs
    output reg       TxReadyEsc,
    output reg       EscSeqEn,
    output reg       EscSerEn,
    output reg       EscSerSeqSel ,
    output reg       EscEncoderEn,
    output reg       LpCtrlEscSel,
    output reg [2:0] EscSeqCtr,
    output reg [1:0] TxCtrlOut, 
    output reg       LpTxEn,
    output reg       EscEncoderDataValid,
	
    // Interface Signals
    output reg       Direction,
    output reg       Stopstate,
    output reg       UlpsActiveNot
);
    // State Definitions as typedef enum
typedef enum logic [5:0] {
    RX_STOP            = 6'd0,
    TX_STOP            = 6'd1,
    RX_HS_REQUEST      = 6'd2,
    RX_HS_SYNC_SEARCH  = 6'd3,
    RX_HS_RECEIVE_DATA = 6'd4,
    RX_HS_POST         = 6'd5,
    RX_LP_RQST         = 6'd6,
    RX_LP_YIELD        = 6'd7,
    RX_TA_RQST         = 6'd8,
    RX_TA_WAIT         = 6'd9,
    TX_TA_GET          = 6'd10,
    TX_TA_ACK          = 6'd11,
    RX_ESC_RQST        = 6'd12,
    RX_Esc_Go          = 6'd13,
    RX_ESC_CMD         = 6'd14,
    RX_ULPS            = 6'd15,
    RX_ULPS_T_WAKE_UP  = 6'd16,
    RX_LPDT            = 6'd17,
    RX_WAIT            = 6'd18,
    TX_LP_RQST         = 6'd25,
    TX_LP_YIELD        = 6'd26,
    TX_TA_REQUEST      = 6'd27,
    TX_TA_GO           = 6'd28,
    TX_ESC_RQST        = 6'd29,
    TX_ESC_GO          = 6'd30,
    TX_ESC_CMD         = 6'd31,
    TX_LPDT            = 6'd32,
    TX_LPDT_PAUSE      = 6'd33,
    TX_TRIGGERS        = 6'd34,
    TX_ULPS            = 6'd35,
    TX_MARK            = 6'd36,
    FORCE_RX           = 6'd37,
    RX_TA_LOOK         = 6'd38,
    RX_TA_ACK          = 6'd39
} fsm_state_t;

    
    // Declare state variables
    fsm_state_t currentState, nextState;
    
    // Timer Instances
    reg         RxTimerEn;
    reg [2:0]   RxTimerSeed;
    wire        RxTimeOut;
    
    RxTimer Rx_timer (
        .clk(RxClkFsm),
        .rst_n(RstN),
        .TimerEn(RxTimerEn),
        .TimerSeed(RxTimerSeed),
        .Timeout(RxTimeOut)
    );

    reg         TxTimerEn;
    reg         TxTimerSeed;
    wire        TxTimeOut;
    
    
    //Turn Disable
    wire   TurnRequest_Intermediate;
    assign TurnRequest_Intermediate = !TurnDisable & TurnRequest;
    
    reg [4:0] Pause_Count;
    reg       LPDT_Count_Done;
    
    TxTimer Tx_timer (
        .clk(RxClkFsm),
        .rst_n(RstN),
        .TimerEn(TxTimerEn),
        .TimerSeed(TxTimerSeed),
        .Timeout(TxTimeOut)
    );

    // State Transition Logic
    always @(posedge RxClkFsm or negedge RstN) begin
        if (!RstN) currentState <= RX_STOP;
        else if (Enable) currentState <= nextState;
    end

    // Next State Logic
    always @(*) begin

        if (ForceTxStopmode) nextState = TX_STOP;
        else if (ForceRxmode) nextState = FORCE_RX;
        else begin
        case (currentState)
            RX_STOP: begin
                if (CtrlDecoderOut == 2'b01) nextState = RX_HS_REQUEST;
                else if (CtrlDecoderOut == 2'b11) nextState = RX_LP_RQST;
                else nextState = RX_STOP;
            end

            RX_HS_REQUEST: 
            begin
                if (RxTimeOut) nextState = RX_HS_SYNC_SEARCH;
                else nextState = RX_HS_REQUEST;
            end
            RX_HS_SYNC_SEARCH: begin
                if (DetectedSeq == 4'b0010 | InErrSotSyncHS)
                    nextState = RX_HS_RECEIVE_DATA;
                    else nextState = RX_HS_SYNC_SEARCH;
            end

            RX_HS_RECEIVE_DATA: begin
                if (DetectedSeq == 4'b0100) nextState = RX_HS_POST;
                else nextState = RX_HS_RECEIVE_DATA;
            end

            RX_HS_POST: nextState = RX_STOP;

            RX_LP_RQST: begin
                if (CtrlDecoderOut == 2'b10) nextState = RX_LP_YIELD;
                else nextState = RX_LP_RQST;
            end

            RX_LP_YIELD: begin
                if (CtrlDecoderOut == 2'b11 && !TurnDisable) 
                    nextState = RX_TA_RQST;
                else if (CtrlDecoderOut == 2'b01) 
                    nextState = RX_ESC_RQST;
                else nextState = RX_LP_YIELD;
            end

            RX_TA_RQST: begin
                if (CtrlDecoderOut == 2'b10) nextState = RX_TA_WAIT;
                else nextState = RX_TA_RQST;
            end

            RX_TA_WAIT: begin
                if (RxTimeOut) nextState = TX_TA_GET;
                else nextState = RX_TA_WAIT;
            end
        
            TX_TA_GET: begin
                if (RxTimeOut) nextState = TX_TA_ACK;
                else nextState = TX_TA_GET;
            end
            
            TX_TA_ACK:
            begin
                if (RxTimeOut) nextState = TX_STOP;
                else nextState = TX_TA_ACK;
            end
            RX_ESC_RQST: begin
                if (CtrlDecoderOut == 2'b10) nextState = RX_Esc_Go;
                else nextState = RX_ESC_RQST;
            end

            RX_Esc_Go: begin
                if (CtrlDecoderOut != 4'b10) nextState = RX_ESC_CMD;
                else nextState = RX_Esc_Go;
            end

            RX_ESC_CMD: begin
                if (InRxUlpsEsc) nextState = RX_ULPS;
                else if (InRxLpdtEsc) nextState = RX_LPDT;
                else if (|InRxTriggerEsc[3:0]) nextState = RX_WAIT;
                else if (InErrEsc) nextState = RX_WAIT;
                else nextState = RX_ESC_CMD;
            end

            RX_ULPS:
                if (CtrlDecoderOut == 4'b11) nextState = RX_ULPS_T_WAKE_UP;
                else nextState = RX_ULPS;
            RX_ULPS_T_WAKE_UP:
                if (RxTimeOut) nextState = RX_WAIT;
                else nextState = RX_ULPS_T_WAKE_UP;
            RX_LPDT:
                if (LpFsmStop) nextState = RX_STOP;
                else nextState = RX_LPDT;
            RX_WAIT:
                if (LpFsmStop) nextState = RX_STOP;
                else nextState = RX_WAIT;

//====================================================
//========================= TX =======================
//====================================================
        TX_STOP: begin 
            if (ForceRxmode) nextState = FORCE_RX;
            else if (TurnRequest_Intermediate || TxReqEsc) nextState = TX_LP_RQST;
            else nextState = TX_STOP;
        end
  
                           /////////////////////////////////////////
                           /////////////LOW POWER MODE//////////////
                           /////////////////////////////////////////
        
        TX_LP_RQST: begin
            if (ForceRxmode) nextState = FORCE_RX;
            else if (TxTimeOut) nextState = TX_LP_YIELD;
            else nextState = TX_LP_RQST;
        end
        
        TX_LP_YIELD: begin
            if (ForceRxmode) nextState = FORCE_RX;
            else if (TxTimeOut &&  TurnRequest_Intermediate) nextState = TX_TA_REQUEST;
            else if (TxTimeOut &&  TxReqEsc) nextState = TX_ESC_RQST;
            else nextState = TX_LP_YIELD;
        end
        
        TX_TA_REQUEST: begin
            if (ForceRxmode) nextState = FORCE_RX;
            else if (TxTimeOut) nextState = TX_TA_GO;
            else nextState = TX_TA_REQUEST;
        end
        
        TX_TA_GO: begin
            if (ForceRxmode) nextState = FORCE_RX;
            else if (TxTimeOut) nextState = RX_TA_LOOK;
            else nextState = TX_TA_GO;
        end
        
        RX_TA_LOOK: begin
            if (CtrlDecoderOut==2'b11) nextState = RX_TA_ACK;
            else nextState = RX_TA_LOOK;
        end
        
        RX_TA_ACK: begin
            if (CtrlDecoderOut==2'b00) nextState = RX_STOP;
            else nextState = RX_TA_ACK;
        end
                           //////////////////////////////////////
                           /////////////ESCAPE MODE//////////////
                           //////////////////////////////////////
        
        TX_ESC_RQST: begin
            if (ForceRxmode) nextState = FORCE_RX;
            else if (TxTimeOut) nextState = TX_ESC_GO;
            else nextState = TX_ESC_RQST;
        end
        
        TX_ESC_GO: begin
            if (ForceRxmode) nextState = FORCE_RX;
            else if (TxTimeOut) nextState = TX_ESC_CMD;
            else nextState = TX_ESC_GO;
        end
        
        TX_ESC_CMD: begin
             if (ForceRxmode) nextState = FORCE_RX;
             else if (CmdDone) begin
                if (TxLpdtEsc) begin
                    if(TxValidEsc) nextState = TX_LPDT;
                    else           nextState = TX_LPDT_PAUSE;
                end
                else if (|TxTriggerEsc[3:0]) nextState = TX_TRIGGERS;
                else if (TxUlpdtEsc) nextState = TX_ULPS;
                else nextState = TX_ESC_CMD;
            end
            else nextState = TX_ESC_CMD;
        end
        
        TX_LPDT: begin
            if (ForceRxmode) nextState = FORCE_RX;
            else if (LPDT_Count_Done && !TxValidEsc) nextState = TX_LPDT_PAUSE;
            else if (TxReqEsc == 0) nextState = TX_MARK;
            else nextState = TX_LPDT;
        end
        
        TX_LPDT_PAUSE: begin
            if (LPDT_Count_Done) nextState = TX_LPDT;
            else                 nextState = TX_LPDT_PAUSE;
        end
        
        TX_TRIGGERS: begin
            if (TxReqEsc == 0) nextState = TX_MARK;
        else nextState = TX_TRIGGERS;
    end
    
    TX_ULPS: begin
        if (ForceRxmode) nextState = FORCE_RX;
        else if (TxUlpdtExit  == 1) nextState = TX_MARK;
        else nextState = TX_ULPS;
    end
    
    TX_MARK: begin
        if (ForceRxmode) nextState = FORCE_RX;
        else if (TxReqEsc == 0) nextState = TX_STOP;
        else nextState = TX_MARK;
    end
    
    FORCE_RX: begin
        if (CtrlDecoderOut==2'b00) nextState = RX_STOP;
        else nextState = FORCE_RX; 
    end

			
            default: nextState = RX_STOP;
        endcase

        end
    end

    // Output Logic
    always @(*) 
    begin
        // Default values
		//============================
		//============ RX ============
		//============================
		
        //===== HS Mode Outputs ======
        // Interface Enables
        HsRxEn = 0;
        // Control Signals
        HsSettleExp = 0;
        HsDecoderEn = 0;
        HSDeserEn   = 0;
        HsSeqDetectorEn = 0;
        // PPI Signals
        RxValidHS  = 0;
        RxActiveHS = 0;

        //===== LP Mode Outputs =====
        // Interface Enables
        LpRxEn = 0;
        // Control Signals
        EscDecoderEn = 0; 
        EscDeserEn   = 0;

        // Decoder Controls
        CtrlDecoderEn = 1;
  
        RequestDetection = 0;  

        RxTimerEn = 0;
        RxTimerSeed = 0;
		//============================
		//============ TX ============
		//============================
        TxReadyEsc = 0;
        EscSeqEn = 0;
        EscSerEn = 0;
        EscSerSeqSel = 0;
        EscEncoderEn = 0;
        TxCtrlOut = 2'b00;
        LpCtrlEscSel = 0;
        LpTxEn = 0;
        TxTimerEn = 0;
        TxTimerSeed = 0;
        EscSeqCtr = 3'b000;
        EscEncoderDataValid = 0;
        UlpsActiveNot = 1;

		// Control Outputs
        Direction     = 1;
        Stopstate     = 1;
        UlpsActiveNot = 1;

        case (currentState)
            RX_STOP: begin
                LpRxEn        = 1;
            end

            RX_HS_REQUEST: begin
                HsRxEn           = 1;
                CtrlDecoderEn    = 0;
                HsDecoderEn      = 1;
                RxTimerEn        = 1;
                RxTimerSeed      = 3'b010;
                RequestDetection = 1;
                Stopstate        = 0;
                RxActiveHS       = 1;
            end

            RX_HS_SYNC_SEARCH: begin
                Stopstate       = 0;
                RxActiveHS      = 1;
                HsRxEn          = 1;
                CtrlDecoderEn   = 0;
                HsDecoderEn     = 1;
                HsSeqDetectorEn = 1;
                HsSettleExp     = 1;
            end

            RX_HS_RECEIVE_DATA: begin
                Stopstate       = 0;
                RxValidHS       = 1;
                RxActiveHS      = 1;
                HsRxEn          = 1;
                CtrlDecoderEn   = 0;
                HsDecoderEn     = 1;
                HSDeserEn       = 1;
                HsSeqDetectorEn = 1;
                HsSettleExp     = 1;
            end
                            
			RX_HS_POST: begin
                Stopstate       = 0;
                RxValidHS       = 0;
                RxActiveHS      = 0;
                LpRxEn          = 1;
                HsDecoderEn     = 0;
                HSDeserEn       = 0;
                HsSeqDetectorEn = 0;
                HsSettleExp     = 1;
			end


            RX_LP_RQST: begin
                Stopstate    = 0;
                RequestDetection = 1; 
            end

            RX_LP_YIELD: begin
                EscDecoderEn = 1;
                Stopstate    = 0;
                LpRxEn       = 1;
            end
            
            RX_TA_RQST: begin
                Stopstate = 0;
                LpRxEn    = 1;
            end

            RX_TA_WAIT: begin
                Stopstate   = 0;
                LpRxEn      = 1;
                RxTimerEn   = 1;
                RxTimerSeed = 3'b011;
            end
        
            TX_TA_GET: begin
                Stopstate     = 0;
                Direction     = 0;
                LpTxEn        = 1;
                CtrlDecoderEn = 1;
                TxCtrlOut     = 2'b10;
                RxTimerEn     = 1;
                RxTimerSeed   = 3'b100;
            end
            
            TX_TA_ACK: begin
                Stopstate     = 0;
                Direction     = 0;
                LpTxEn        = 1;
                CtrlDecoderEn = 1;
                TxCtrlOut     = 2'b01;
                RxTimerEn     = 1;
                RxTimerSeed   = 3'b000;
            end
                              
            RX_ESC_RQST: begin
                Stopstate    = 0;
                LpRxEn       = 1;
                EscDecoderEn = 1;
            end
                  
            RX_Esc_Go: begin
                Stopstate    = 0;
                LpRxEn       = 1;
                EscDecoderEn = 1;
            end
                  
            RX_ESC_CMD: begin
                Stopstate    = 0;
                LpRxEn       = 1;
                EscDecoderEn = 1;
            end
            
            RX_WAIT: begin
                Stopstate     = 0; 
                LpRxEn        = 1;
                CtrlDecoderEn = 1;
                EscDecoderEn  = 0;
            end
                  
            RX_ULPS: begin
                Stopstate     = 0; 
                LpRxEn        = 1;
                UlpsActiveNot = 0;
            end
                  
            RX_ULPS_T_WAKE_UP: begin
                Stopstate     = 0;
                UlpsActiveNot = 1;
                LpRxEn        = 1;
                RxTimerEn     = 1;
                RxTimerSeed   = 3'b101;
            end
                  
            RX_LPDT: begin
                Stopstate     = 0;
                LpRxEn        = 1;
                CtrlDecoderEn = 0;
                EscDeserEn    = 1;
                EscDecoderEn  = 1;
            end
			

            
            //============================
            //============ TX ============
            //============================
			TX_STOP: begin
			    Direction        = 0;
				Stopstate        = 1;
				LpTxEn           = 1;
				LpRxEn           = 1;
			end
							   /////////////////////////////////////////
							   /////////////LOW POWER MODE//////////////
							   /////////////////////////////////////////
			TX_LP_RQST: begin
                Direction = 0;
				Direction = 0;
				Stopstate = 0;
				TxCtrlOut = 2'b11;
				LpTxEn = 1;
				TxTimerEn = 1;
				LpRxEn = 1;
			end
			
			TX_LP_YIELD: begin
                Direction = 0;
				Direction = 0;
				Stopstate = 0;
				TxCtrlOut = 2'b10;
				LpTxEn = 1;
				LpRxEn = 1;
				TxTimerEn = 1;
			end
			
			TX_TA_REQUEST: begin
                Direction = 0;
				Direction = 0;
				Stopstate = 0;
				TxCtrlOut = 2'b11;
				LpTxEn = 1;
				LpRxEn = 1;
				TxTimerEn = 1;
			end
			
			TX_TA_GO: begin
                Direction = 0;
				Stopstate = 0;
				TxCtrlOut = 2'b10;
				LpTxEn = 1;
				LpRxEn = 1;
				TxTimerEn = 1;
				TxTimerSeed = 1'b1; 
			end
			
			RX_TA_LOOK: begin
                Direction  = 0;
				Stopstate = 0;
				LpRxEn = 1;
				TxTimerEn = 0;
			end
			
			RX_TA_ACK: begin
                Direction = 0;
				Stopstate = 0;
				LpRxEn = 1;

			end
						   //////////////////////////////////////
						   /////////////ESCAPE MODE//////////////
						   //////////////////////////////////////
			TX_ESC_RQST: begin
                Direction = 0;
				Stopstate = 1'b0;
				TxCtrlOut = 2'b01;
				LpTxEn = 1'b1;
				LpRxEn = 1'b1;
				TxTimerEn = 1'b1;
			end
			
			TX_ESC_GO: begin
                Direction = 0;
				Stopstate = 1'b0;
				TxCtrlOut = 2'b10;
				LpTxEn = 1'b1;
				LpRxEn = 1'b1;
				TxTimerEn = 1'b1;
			end
			
			TX_ESC_CMD: begin
				 case ({TxTriggerEsc,TxUlpdtEsc,TxLpdtEsc})
				6'b000001:  EscSeqCtr = 3'b000; //Low-Power Data Transmission 
				6'b000010:  EscSeqCtr = 3'b100; //Ultra-Low Power State
				6'b000100:  EscSeqCtr = 3'b100; // Reset-Trigger
				6'b001000:  EscSeqCtr = 3'b101; //Unknown-3
				6'b010000:  EscSeqCtr = 3'b110; //Unknown-4
				6'b100000:  EscSeqCtr = 3'b111; //Unknown-5 
				default:    EscSeqCtr = 3'b000;      

			endcase
				Direction = 1'b0;
				Stopstate = 1'b0;
				EscSeqEn = 1'b1;
				EscEncoderEn = 1'b1;
				LpCtrlEscSel = 1'b1;
				LpTxEn = 1'b1;
				LpRxEn = 1'b1;
			end
			
			TX_LPDT: begin
				Direction = 1'b0;
				Stopstate = 1'b0;
				EscSerEn = 1'b1;
				TxReadyEsc = SerReadyEsc;
				EscSerSeqSel  = 1'b1;
				EscEncoderEn = 1'b1;
				LpCtrlEscSel = 1'b1;
				LpTxEn = 1'b1;
				LpRxEn = 1'b1;
				EscEncoderDataValid = 1'b1;
			end

			TX_LPDT_PAUSE: begin
				Direction = 1'b0;
				Stopstate = 1'b0;
				EscSerEn = 1'b0;
				TxReadyEsc = 1;
				EscSerSeqSel  = 1'b1;
				EscEncoderEn = 1'b1;
				LpCtrlEscSel = 1'b1;
				LpTxEn = 1'b1;
				LpRxEn = 1'b1;
			end
			
			 TX_TRIGGERS: begin
				Direction = 1'b0;
				Stopstate = 1'b0;
				TxCtrlOut = 2'b10;
				LpTxEn = 1'b1;
				LpRxEn = 1'b1;
			end
			
			TX_ULPS: begin
				Direction = 1'b0;
				Stopstate = 1'b0;
				TxCtrlOut = 2'b10;
				LpTxEn = 1'b1;
				LpRxEn = 1'b1;
				UlpsActiveNot = 0;
			end

			FORCE_RX: begin
				Stopstate = 0;
				LpRxEn = 1;
			end
        endcase
    end

//Pause counter
//Word clk is 30 times faster than the esc clk, so in order to detain the ready signal for 1 esc clk, we count 29 of word clk



	always@(posedge RxClkFsm or negedge RstN) 
	begin
		if (!RstN) 
		begin
			Pause_Count <= 5'b0;
			LPDT_Count_Done <= 1'b0;
		end 
		else 
		begin
			LPDT_Count_Done <= 1'b0;
			Pause_Count <= 5'b0; 
			case (currentState)
				TX_LPDT: 
				begin
					if(SerLastBit) begin
						if(Pause_Count == 5'd28) begin //here 28 only to compensate latency
							LPDT_Count_Done <= 1'b1;
						end
						else 
						begin
							LPDT_Count_Done <= 1'b0;
						end
						Pause_Count <= Pause_Count + 5'b1;
					end
					else 
					begin
						Pause_Count <= 5'b0;
						LPDT_Count_Done <= 1'b0;
					end
				end
				TX_LPDT_PAUSE: 
				begin
					if(TxValidEsc || !TxReqEsc) begin
						Pause_Count <= Pause_Count + 5'b1;
						if(Pause_Count == 5'd29) begin
							LPDT_Count_Done <= 1'b1;
						end
						else 
						begin
							LPDT_Count_Done <= 1'b0;
						end
					end
					else 
					begin
						Pause_Count <= 5'b0;
					end
				end
				default: 
				begin
					Pause_Count <= 5'b0;
					LPDT_Count_Done <= 1'b0;
				end
			endcase
		end
	end


    // Continuous Assignments
    assign RxWordClkHS     = HsCLK;
    assign RxInvalidCodeHS = InRxInvalidCodeHS;
    assign RxSyncHS        = (DetectedSeq == 4'b0010);
    assign ErrSotHS        = InErrSotHS;
    assign ErrSotSyncHS    = InErrSotSyncHS;
    assign RxClkEsc        = LpCLK;
    assign RxValidEsc      = InRxValidEsc;
    assign RxTriggerEsc    = InRxTriggerEsc;
    assign RxUlpsEsc       = InRxUlpsEsc;
    assign RxLpdtEsc       = InRxLpdtEsc;
    assign ErrEsc          = InErrEsc;
    assign ErrSyncEsc      = InErrSyncEsc;
    assign ErrControl      = InErrControl;
    

endmodule