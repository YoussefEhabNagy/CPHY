module cphy_tx_fsm (
   ////////// input signals TX //////////
    // Interface Signals
    input wire RstN,
    input wire TxWordClkHS,
    input wire TxReqHS,
    input wire TxSendSyncHS,
    input wire TxReqEsc,
    input wire TxValidEsc,
    input wire TxUlpsEsc,
    input wire TxLpdtEsc,
    input wire TxUlpsExit,
    input wire [3:0]TxTriggerEsc,
    // Control Signals
    input wire TurnRequest,
    input wire ForceRxmode,
    input wire ForceTxStopmode,
    input wire TurnDisable,
    input wire Enable,
    //HS_Sequencer signal  
    input wire SeqDone,
    //Esc_Sequencer signal  
    input wire CmdDone,
    //ESC_Serializer signal  
    input wire SerReadyEsc,
    input wire SerLastBit,
/////////////////// input signals RX /////////////////////////
    input  wire       LpCLK,
    input  wire       LpFsmStop,
    input  wire [1:0] LpState,
    input  wire [3:0] InRxTriggerEsc,
    input  wire       InRxUlpsEsc,
    input  wire       InRxLpdtEsc,
    input  wire       InErrEsc,

/////////////////// Output signals TX///////////////////////////
    // HS Mode Outputs
    output reg TxReadyHS,
    output reg [2:0] HsSeqCtr,
    output reg HsSerializerEn,
    output reg SerSeqSel,
    output reg EncoderEn,
    output reg HsTxEn,
    // ESC Mode Outputs
    output reg TxReadyEsc,
    output reg EscSerEn,
    output reg EscSerSeqSel ,
    output reg EscEncoderEn,
    output reg LpCtrlEscSel,
    output reg [7:0] EscSeqCtr,
    output reg [1:0] TxCtrlOut, 
    output reg LpTxEn,
    output reg Pause_Ready,
    // Interface Signals
    output reg Direction,
    output reg Stopstate,
    output reg UlpsActiveNot,
    output reg EscEncoderDataValid,
    output reg TxRequestHSSEQ,

 /////////////////// Output signals RX ///////////////////////////
    output reg        LpRxEn,
    output reg        EscDecoderEn, 
    output wire       RxClkEsc,
    output reg        CtrlDecoderEn,
    output reg        RequestDetection// this flag to alerts Esc_Decoder if i have request (HS - LP) 

);
typedef enum logic [5:0] {
    TX_STOP             = 6'd0,
    TX_HS_REQUEST       = 6'd1,
    TX_LP_RQST          = 6'd2,
    TX_HS_PREPARE       = 6'd3,
    TX_LP_YIELD         = 6'd4,   
    TX_HS_PREAMBLE      = 6'd5,
    TX_TA_REQUEST       = 6'd6,
    TX_ESC_RQST         = 6'd7,  
    TX_HS_SYNC_WORD     = 6'd8,
    TX_TA_GO            = 6'd9,
    TX_HS_SEND_DATA     = 6'd10,
    TX_HS_POST          = 6'd11,
    RX_TA_LOOK          = 6'd12,
    RX_TA_ACK           = 6'd13,
    RX_STOP             = 6'd14,
    RX_LP_RQST          = 6'd15,
    RX_LP_YIELD         = 6'd16,
    RX_TA_RQST          = 6'd17,
    RX_TA_WAIT          = 6'd18,
    TX_TA_GET           = 6'd19,
    TX_TA_ACK           = 6'd20,
    RX_ESC_RQST         = 6'd21,
    RX_Esc_Go           = 6'd22,
    RX_ESC_CMD          = 6'd23,
    RX_ULPS             = 6'd24,
    RX_ULPS_T_WAKE_UP   = 6'd25,
    RX_LPDT             = 6'd26,
    RX_WAIT             = 6'd27,
    FORCE_RX            = 6'd28,
    TX_ESC_GO           = 6'd29, 
    TX_ESC_CMD          = 6'd30, 
    TX_LPDT             = 6'd31,  
    TX_TRIGGERS         = 6'd32,  
    TX_ULPS             = 6'd33,  
    TX_MARK             = 6'd34,
    TX_LPDT_Pause       = 6'd35
} state_t;


state_t current_state, next_state, next_state_Intermediate;
reg [6:0] Pause_Count;
reg       LPDT_Count_Done;
reg       First_Byte_Flag;
reg       Pause_Ready_Reg;
/*
reg TxReadyHS;
reg [2:0] HsSeqCtr;
reg HsSerializerEn;
reg SerSeqSel;
reg EncoderEn;
reg HsTxEn;
reg TxReadyEsc;
reg EscSerEn;
reg EscSerSeqSel;
reg EscEncoderEn;
reg LpCtrlEscSel;
reg [7:0] EscSeqCtr;
reg [1:0] TxCtrlOut;
reg LpTxEn;
reg Direction;
reg Stopstate;
reg UlpsActiveNot;
reg EscEncoderDataValid;
reg LpRxEn;
reg EscDecoderEn;
reg CtrlDecoderEn;
reg RequestDetection;
reg Timer_En;
reg Timer_Seed;
reg RxTimerEn;
reg RxTimerSeed;
*/

//========== Timers instance ===========
// TX Timer Controls
reg  Timer_En;
reg  Timer_Seed;
wire TimeOut;
// RX Timer Controls
reg         RxTimerEn;
reg [2:0]   RxTimerSeed;
wire        RxTimeOut;

TxTimer timer_inst (
    .clk(TxWordClkHS),
    .RstN(RstN),
    .TimerEn(Timer_En),
    .TimerSeed(Timer_Seed),
    .Timeout(TimeOut)
);

RxTimer Rx_timer (
      .clk(TxWordClkHS),
      .rst_n(RstN),
      .TimerEn(RxTimerEn),
      .TimerSeed(RxTimerSeed),
      .Timeout(RxTimeOut)
  );

    
    // Continuous Assignments
    assign RxClkEsc        = LpCLK;
    assign RxTriggerEsc    = InRxTriggerEsc;
    assign RxUlpsEsc       = InRxUlpsEsc;
    assign RxLpdtEsc       = InRxLpdtEsc;
    assign ErrEsc          = InErrEsc;

// State transition logic
always @(posedge TxWordClkHS or negedge RstN) begin
    if (!RstN) begin
        current_state <= TX_STOP;
    end else begin
        current_state <= next_state_Intermediate;
    end
end
always @(posedge TxWordClkHS or negedge RstN) begin
    if (!RstN) begin
        Pause_Ready_Reg <= 0;
    end else begin
        Pause_Ready_Reg <= Pause_Ready;
    end
end

// Force TxStopMode
always @(*) begin
    if(ForceTxStopmode)
        next_state_Intermediate = TX_STOP;
    else
        next_state_Intermediate = next_state;
end

//Turn Disable

wire   TurnRequest_Intermediate;
assign TurnRequest_Intermediate = !TurnDisable & TurnRequest;

//Esc Seq

reg [7:0] EscSeqCtr_Intermediate;

// Next state logic
always @(*) begin
    case (current_state)
        TX_STOP: begin 
            if (ForceRxmode) next_state = FORCE_RX;
            else if (TurnRequest_Intermediate || TxReqEsc) next_state = TX_LP_RQST;
            else if (TxReqHS) next_state = TX_HS_REQUEST;
            else next_state = TX_STOP;
        end

        TX_HS_REQUEST: begin
            if (ForceRxmode) next_state = FORCE_RX;
            else if (TimeOut) next_state = TX_HS_PREPARE;
            else next_state = TX_HS_REQUEST;
        end

        TX_HS_PREPARE: begin
            if (ForceRxmode) next_state = FORCE_RX;
            else if (TimeOut) next_state = TX_HS_PREAMBLE;
            else next_state = TX_HS_PREPARE;
        end
        
        TX_HS_PREAMBLE: begin
            if (ForceRxmode) next_state = FORCE_RX;
            else if (SeqDone == 1) next_state = TX_HS_SEND_DATA;
            else next_state = TX_HS_PREAMBLE;
        end

        TX_HS_SYNC_WORD: begin
            if (ForceRxmode) next_state = FORCE_RX;
            else next_state = TX_HS_SEND_DATA;
        end
       
        TX_HS_SEND_DATA: begin
            if (ForceRxmode) next_state = FORCE_RX;
            else if (TxSendSyncHS) next_state = TX_HS_SYNC_WORD;
            else if (!TxReqHS) next_state = TX_HS_POST;
            else next_state = TX_HS_SEND_DATA;
        end
        
        TX_HS_POST: begin
            if (ForceRxmode) next_state = FORCE_RX;
            else if (SeqDone == 1) next_state = TX_STOP;
            else next_state = TX_HS_POST;
        end

                           /////////////////////////////////////////
                           /////////////LOW POWER MODE//////////////
                           /////////////////////////////////////////

        TX_LP_RQST: begin
            if (ForceRxmode) next_state = FORCE_RX;
            else if (TimeOut) next_state = TX_LP_YIELD;
            else next_state = TX_LP_RQST;
        end
        
        TX_LP_YIELD: begin
            if (ForceRxmode) next_state = FORCE_RX;
            else if (TimeOut &&  TurnRequest_Intermediate) next_state = TX_TA_REQUEST;
            else if (TimeOut &&  TxReqEsc) next_state = TX_ESC_RQST;
            else next_state = TX_LP_YIELD;
        end
        
        TX_TA_REQUEST: begin
            if (ForceRxmode) next_state = FORCE_RX;
            else if (TimeOut) next_state = TX_TA_GO;
            else next_state = TX_TA_REQUEST;
        end
        
        TX_TA_GO: begin
            if (ForceRxmode) next_state = FORCE_RX;
            else if (TimeOut) next_state = RX_TA_LOOK;
            else next_state = TX_TA_GO;
        end
        
        RX_TA_LOOK: begin
            if (LpState==2'b11) next_state = RX_TA_ACK;
            else next_state = RX_TA_LOOK;
        end
        
        RX_TA_ACK: begin
            if (LpState==2'b00) next_state = RX_STOP;
            else next_state = RX_TA_ACK;
        end


                           //////////////////////////////////////
                           /////////////ESCAPE MODE//////////////
                           //////////////////////////////////////
        
        TX_ESC_RQST: begin
            if (ForceRxmode) next_state = FORCE_RX;
            else if (TimeOut) next_state = TX_ESC_GO;
            else next_state = TX_ESC_RQST;
        end
        
        TX_ESC_GO: begin
            if (ForceRxmode) next_state = FORCE_RX;
            else if (TimeOut) next_state = TX_ESC_CMD;
            else next_state = TX_ESC_GO;
        end
        
        TX_ESC_CMD: begin
             if (ForceRxmode) next_state = FORCE_RX;
             else if (CmdDone) begin
                if (TxLpdtEsc) next_state = TX_LPDT;
                else if (|TxTriggerEsc[3:0]) next_state = TX_TRIGGERS;
                else if (TxUlpsEsc ) next_state = TX_ULPS;
                else next_state = TX_ESC_CMD;
            end
            else next_state = TX_ESC_CMD;
        end
        
        TX_LPDT: begin
            if (ForceRxmode) next_state = FORCE_RX;
            else if ((TxReqEsc == 0) && LPDT_Count_Done) next_state = TX_MARK;
            else if (LPDT_Count_Done && !TxValidEsc) next_state = TX_LPDT_Pause;
            else next_state = TX_LPDT;
        end

        TX_LPDT_Pause: begin
            if (LPDT_Count_Done) next_state = TX_LPDT;
            else                 next_state = TX_LPDT_Pause;
        end
        
        TX_TRIGGERS: begin
            if (TxReqEsc == 0) next_state = TX_MARK;
            else next_state = TX_TRIGGERS;
        end
        
        TX_ULPS: begin
            if (ForceRxmode) next_state = FORCE_RX;
            else if (TxUlpsExit             == 1) next_state = TX_MARK;
            else next_state = TX_ULPS;
        end
        
        TX_MARK: begin
            if (ForceRxmode) next_state = FORCE_RX;
            else if (LPDT_Count_Done) next_state = TX_STOP;
            else next_state = TX_MARK;
        end
        
        FORCE_RX: begin
            if (LpState==2'b00) next_state = RX_STOP;
            else next_state = FORCE_RX; 
        end

//====================================================
//========================= RX =======================
//====================================================      
            RX_STOP: begin
                if (LpState == 2'b11) next_state = RX_LP_RQST;
                else next_state = RX_STOP;
            end
            RX_LP_RQST: begin
                if (LpState == 2'b10) next_state = RX_LP_YIELD;
                else next_state = RX_LP_RQST;
            end

            RX_LP_YIELD: begin
                if (LpState == 2'b11 && !TurnDisable) 
                    next_state = RX_TA_RQST;
                else if (LpState == 2'b01) 
                    next_state = RX_ESC_RQST;
                else next_state = RX_LP_YIELD;
            end

            RX_TA_RQST: begin
                if (LpState == 2'b10) next_state = RX_TA_WAIT;
                else next_state = RX_TA_RQST;
            end

            RX_TA_WAIT: begin
                if (RxTimeOut) next_state = TX_TA_GET;
                else next_state = RX_TA_WAIT;
            end
        
            TX_TA_GET: begin
                if (RxTimeOut) next_state = TX_TA_ACK;
                else next_state = TX_TA_GET;
            end
            
            TX_TA_ACK:
            begin
                if (RxTimeOut) next_state = TX_STOP;
                else next_state = TX_TA_ACK;
            end
            RX_ESC_RQST: begin
                if (LpState == 2'b10) next_state = RX_Esc_Go;
                else next_state = RX_ESC_RQST;
            end

            RX_Esc_Go: begin
                if (LpState != 4'b10) next_state = RX_ESC_CMD;
                else next_state = RX_Esc_Go;
            end

            RX_ESC_CMD: begin
                if (InRxUlpsEsc) next_state = RX_ULPS;
                else if (InRxLpdtEsc) next_state = RX_LPDT;
                else if (|InRxTriggerEsc[3:0]) next_state = RX_WAIT;
                else if (InErrEsc) next_state = RX_WAIT;
                else next_state = RX_ESC_CMD;
            end

            RX_ULPS:
                if (LpState == 4'b11) next_state = RX_ULPS_T_WAKE_UP;
                else next_state = RX_ULPS;
            RX_ULPS_T_WAKE_UP:
                if (RxTimeOut) next_state = RX_WAIT;
                else next_state = RX_ULPS_T_WAKE_UP;
            RX_LPDT:
                if (LpFsmStop) next_state = RX_STOP;
                else next_state = RX_LPDT;
            RX_WAIT:
                if (LpFsmStop) next_state = RX_STOP;
                else next_state = RX_WAIT;

        default: next_state = TX_STOP;
    endcase
end
/*
//Seq output for cdc
always @(posedge TxWordClkHS or negedge RstN)
begin
    if (!RstN) begin
        TxReadyHS           <= 1'b0;
        HsSeqCtr            <= 3'b000;
        HsSerializerEn      <= 1'b0;
        SerSeqSel           <= 1'b0;
        EncoderEn           <= 1'b0;
        HsTxEn              <= 1'b0;
        TxReadyEsc          <= 1'b0;
        EscSerEn            <= 1'b0;
        EscSerSeqSel        <= 1'b0;
        EscEncoderEn        <= 1'b0;
        LpCtrlEscSel        <= 1'b0;
        EscSeqCtr           <= 8'b0;
        TxCtrlOut           <= 2'b00;
        LpTxEn              <= 1'b0;
        Direction           <= 1'b0;
        Stopstate           <= 1'b0;
        UlpsActiveNot       <= 1'b1; 
        EscEncoderDataValid <= 1'b0;
        LpRxEn              <= 1'b0;
        EscDecoderEn        <= 1'b0;
        CtrlDecoderEn       <= 1'b0;
        RequestDetection    <= 1'b0;
        Timer_En            <= 1'b0;
        Timer_Seed          <= 1'b0;
        RxTimerEn           <= 1'b0;
        RxTimerSeed         <= 1'b0;
    end else begin
        TxReadyHS         <= TxReadyHS;
        HsSeqCtr          <= HsSeqCtr;
        HsSerializerEn    <= HsSerializerEn;
        SerSeqSel         <= SerSeqSel;
        EncoderEn         <= EncoderEn;
        HsTxEn            <= HsTxEn;
        TxReadyEsc        <= TxReadyEsc;
        EscSerEn          <= EscSerEn;
        EscSerSeqSel      <= EscSerSeqSel;
        EscEncoderEn      <= EscEncoderEn;
        LpCtrlEscSel      <= LpCtrlEscSel;
        EscSeqCtr         <= EscSeqCtr;
        TxCtrlOut         <= TxCtrlOut;
        LpTxEn            <= LpTxEn;
        Direction         <= Direction;
        Stopstate         <= Stopstate;
        UlpsActiveNot     <= UlpsActiveNot;
        EscEncoderDataValid <= EscEncoderDataValid;
        LpRxEn            <= LpRxEn;
        EscDecoderEn      <= EscDecoderEn;
        CtrlDecoderEn     <= CtrlDecoderEn;
        RequestDetection  <= RequestDetection;
        Timer_En          <= Timer_En;
        Timer_Seed        <= Timer_Seed;
        RxTimerEn         <= RxTimerEn;
        RxTimerSeed       <= RxTimerSeed;
    end
end
*/
// Output logic (Moore FSM)
always @(*) begin
//============================================
//============ TX Default outputs ============
//============================================
    HsSerializerEn = 0;
    SerSeqSel = 0;
    EncoderEn = 0;
    TxReadyHS = 0;
    TxReadyEsc = 0;
    Direction = 0;
    Stopstate = 0;
    EscSerEn = 0;
    EscSerSeqSel = 0;
    EscEncoderEn = 0;
    TxCtrlOut = 2'b00;
    LpCtrlEscSel = 0;
    LpTxEn = 0;
    HsTxEn = 0;
    LpRxEn = 0;
    Timer_En = 0;
    Timer_Seed = 0;
    HsSeqCtr = 3'b000;
    EscSeqCtr = 7'b0;
    EscEncoderDataValid = 0;
    UlpsActiveNot = 1;
    TxRequestHSSEQ = TxReqHS;
    Pause_Ready = 0;
//============================================
//============ RX Default outputs ============
//============================================
        //===== LP Mode Outputs =====
        // Control Signals
        EscDecoderEn = 0; 
        // Decoder Controls
        CtrlDecoderEn = 1;
        RequestDetection = 0;  
        RxTimerEn = 0;
        RxTimerSeed = 0;
/////////////////////////////////////////////////////////////////////////////////////
    case (current_state)
//============================================
//============ TX outputs ====================
//============================================
        TX_STOP: begin
            Stopstate = 1;
            LpTxEn = 1;
            LpRxEn = 1;
        end
        
        TX_HS_REQUEST: begin
            Stopstate = 0;
            TxCtrlOut = 2'b01;
            LpTxEn = 1;
            Timer_En = 1;
        end
        
        TX_HS_PREPARE: begin
            Stopstate = 0;
            TxCtrlOut = 2'b10;
            LpTxEn = 1;
            Timer_En = 1;
        end
        
        TX_HS_PREAMBLE: begin
            Stopstate = 0;
            TxCtrlOut = 2'b10;
            HsSeqCtr = 3'b100;
            EncoderEn = 1;
            HsTxEn = 1;
        end
        
        TX_HS_SYNC_WORD: begin
            TxReadyHS = 1;
            TxCtrlOut = 2'b10;
            Stopstate = 0;
            HsSeqCtr = 3'b010;
            EncoderEn = 1;
            HsTxEn = 1;
        end
       
        TX_HS_SEND_DATA: begin
            TxReadyHS = 1;
            TxCtrlOut = 2'b10;
            Stopstate = 0;
            HsSerializerEn = 1;
            SerSeqSel = 1;
            EncoderEn = 1;
            HsTxEn = 1;
        end
        
        TX_HS_POST: begin
            Stopstate = 0;
            TxCtrlOut = 2'b10;
            HsSeqCtr = 3'b001;          
            HsTxEn = 1;
            EncoderEn = 1;
        end
                           /////////////////////////////////////////
                           /////////////LOW POWER MODE//////////////
                           /////////////////////////////////////////
        TX_LP_RQST: begin
            Direction = 0;
            Stopstate = 0;
            TxCtrlOut = 2'b11;
            LpTxEn = 1;
            Timer_En = 1;
            LpRxEn = 1;
        end
        
        TX_LP_YIELD: begin
            Direction = 0;
            Stopstate = 0;
            TxCtrlOut = 2'b10;
            LpTxEn = 1;
            LpRxEn = 1;
            Timer_En = 1;
        end
        
        TX_TA_REQUEST: begin
            Direction = 0;
            Stopstate = 0;
            TxCtrlOut = 2'b11;
            LpTxEn = 1;
            LpRxEn = 1;
            Timer_En = 1;
        end
        
        TX_TA_GO: begin
            Direction = 0;
            Stopstate = 0;
            TxCtrlOut = 2'b10;
            LpTxEn = 1;
            LpRxEn = 1;
            Timer_En = 1;
            Timer_Seed = 1'b1; 
        end
        
        RX_TA_LOOK: begin
            Direction = 1;
            Stopstate = 0;
            LpRxEn = 1;
            CtrlDecoderEn = 1;
            Timer_En = 0;
        end
        
        RX_TA_ACK: begin
            Direction = 1;
            Stopstate = 0;
            LpRxEn = 1;
            CtrlDecoderEn = 1;
        end
                       //////////////////////////////////////
                       /////////////ESCAPE MODE//////////////
                       //////////////////////////////////////
        TX_ESC_RQST: begin
            Direction = 1'b0;
            Stopstate = 1'b0;
            EscEncoderEn = 1'b1;
            TxCtrlOut = 2'b01;
            LpTxEn = 1'b1;
            LpRxEn = 1'b1;
            EscEncoderDataValid = 1'b1;
            Timer_En = 1'b1;
            EscSeqCtr = EscSeqCtr_Intermediate;
        end
        
        TX_ESC_GO: begin
            Direction = 1'b0;
            Stopstate = 1'b0;
            EscEncoderEn = 1'b1;
            TxCtrlOut = 2'b10;
            LpTxEn = 1'b1;
            LpRxEn = 1'b1;
            EscEncoderDataValid = 1'b1;
            Timer_En = 1'b1;
            EscSeqCtr = EscSeqCtr_Intermediate;
        end
        
        TX_ESC_CMD: begin
            Direction = 1'b0;
            Stopstate = 1'b0;
            EscEncoderEn = 1'b1;
            LpCtrlEscSel = 1'b1;
            LpTxEn = 1'b1;
            LpRxEn = 1'b1;
            EscEncoderDataValid = 1'b1;
            EscSeqCtr = EscSeqCtr_Intermediate;
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
            Pause_Ready = Pause_Ready_Reg;
        end

        TX_LPDT_Pause: begin
            Direction = 1'b0;
            Stopstate = 1'b0;
            EscSerEn = 1'b0;
            TxReadyEsc = SerReadyEsc;
            EscSerSeqSel  = 1'b1;
            EscEncoderEn = 1'b1;
            LpCtrlEscSel = 1'b1;
            LpTxEn = 1'b1;
            LpRxEn = 1'b1;
            Pause_Ready = 1'b1;
        end
        
        TX_MARK: begin
            Direction = 1'b0;
            Stopstate = 1'b0;
            EscSerEn = 1'b0;
            TxReadyEsc = 0;
            TxCtrlOut = 2'b11;
            LpTxEn = 1'b1;
            LpRxEn = 1'b1;
        end

        TX_TRIGGERS: begin
            Direction = 1'b0;
            Stopstate = 1'b0;
            EscEncoderEn = 1'b1;
            LpCtrlEscSel = 1'b1;
            LpTxEn = 1'b1;
            LpRxEn = 1'b1;
        end
        
        TX_ULPS: begin
            Direction = 1'b0;
            Stopstate = 1'b0;
            EscEncoderEn = 1'b1;
            LpCtrlEscSel = 1'b1;
            LpTxEn = 1'b1;
            LpRxEn = 1'b1;
            UlpsActiveNot = 0;
        end

        FORCE_RX: begin
            Direction = 1;
            Stopstate = 0;
            LpRxEn = 1;
            CtrlDecoderEn = 1; 
        end
//============================================
//============ RX outputs ====================
//============================================
       
            RX_STOP: begin
                LpRxEn        = 1;
                Direction     = 1;
                Stopstate     = 1;
            end
                           /////////////////////////////////////////
                           /////////////LOW POWER MODE//////////////
                           /////////////////////////////////////////

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
                EscDecoderEn  = 1;
            end
			
            default: begin
                //============================================
                //============ TX Default outputs ============
                //============================================
                    HsSerializerEn = 0;
                    SerSeqSel = 0;
                    EncoderEn = 0;
                    TxReadyHS = 0;
                    TxReadyEsc = 0;
                    Direction = 0;
                    Stopstate = 0;
                    EscSerEn = 0;
                    EscSerSeqSel = 0;
                    EscEncoderEn = 0;
                    TxCtrlOut = 2'b00;
                    LpCtrlEscSel = 0;
                    LpTxEn = 0;
                    HsTxEn = 0;
                    LpRxEn = 0;
                    EscDecoderEn = 0;
                    Timer_En = 0;
                    Timer_Seed = 0;
                    HsSeqCtr = 3'b000;
                    EscSeqCtr = 7'b000;
                    EscEncoderDataValid = 0;
                    UlpsActiveNot = 1;
                    TxRequestHSSEQ = TxReqHS;
                //============================================
                //============ RX Default outputs ============
                //============================================
					//===== LP Mode Outputs =====
					// Control Signals
					EscDecoderEn = 0; 
					// Decoder Controls
					CtrlDecoderEn = 1;
					RequestDetection = 0;  
					RxTimerEn = 0;
					RxTimerSeed = 0;
                ///////////////////////////////////////////////////////////////////////////////////
            end
			


    endcase
end


    // Continuous Assignments
    assign RxClkEsc        = LpCLK;

//Esc Sequencer control

always @(*) begin
    case ({TxTriggerEsc           ,TxUlpsEsc      ,TxLpdtEsc})
        6'b000001:  EscSeqCtr_Intermediate = 8'b00000001; //Low-Power Data Transmission 
        6'b000010:  EscSeqCtr_Intermediate = 8'b00000010; //Ultra-Low Power State
        6'b000100:  EscSeqCtr_Intermediate = 8'b00010000; // Reset-Trigger
        6'b001000:  EscSeqCtr_Intermediate = 8'b00100000; //Unknown-3
        6'b010000:  EscSeqCtr_Intermediate = 8'b01000000; //Unknown-4
        6'b100000:  EscSeqCtr_Intermediate = 8'b10000000; //Unknown-5 
        default:    EscSeqCtr_Intermediate = 8'b00000000;      
    endcase
end

//Pause counter
//Word clk is 30 times faster than the esc clk, so in order to detain the ready signal for 1 esc clk, we count 29 of word clk



always @(posedge TxWordClkHS or negedge RstN) begin
    if (!RstN) begin
        Pause_Count <= 7'b0;
        LPDT_Count_Done <= 1'b0;
        First_Byte_Flag <= 1'b0;
    end else begin
        LPDT_Count_Done <= 1'b0;
        Pause_Count <= 7'b0; 
        case (current_state)
            TX_LPDT: begin
                First_Byte_Flag <= First_Byte_Flag | TxValidEsc;
                if(SerLastBit || !First_Byte_Flag) begin
                    if(Pause_Count == 7'd28) begin //here 28 only to combensate latency
                        LPDT_Count_Done <= 1'b1;
                        Pause_Count <= 1'b0;
                    end
                    else begin
                        LPDT_Count_Done <= 1'b0;
                        Pause_Count <= Pause_Count + 7'b1;
                    end
                end
                else begin
                    Pause_Count <= 7'b0;
                    LPDT_Count_Done <= 1'b0;
                end
            end
            TX_LPDT_Pause: begin
                First_Byte_Flag <= 1'b0;
                if(!TxReqEsc) begin
                    Pause_Count <= Pause_Count + 5'b1;
                    if(Pause_Count == 7'd98) begin
                        LPDT_Count_Done <= 1'b1;
                        Pause_Count <= 0;
                    end
                    else begin
                        LPDT_Count_Done <= 1'b0;
                    end
                end else if(TxValidEsc) begin
                    Pause_Count <= Pause_Count + 7'b1;
                    if(Pause_Count == 7'd29) begin
                        LPDT_Count_Done <= 1'b1;
                    end
                    else begin
                        LPDT_Count_Done <= 1'b0;
                    end
                end
                else begin
                    Pause_Count <= 7'b0;
                end
            end
            TX_MARK: begin
                First_Byte_Flag <= 1'b0;
                Pause_Count <= Pause_Count + 7'b1;
                if(Pause_Count == 7'd25) begin
                    LPDT_Count_Done <= 1'b1;
                end
                else begin
                    LPDT_Count_Done <= 1'b0;
                end
            end
            default: begin
                First_Byte_Flag <= 1'b0;
                Pause_Count <= 6'b0;
                LPDT_Count_Done <= 1'b0;
            end
        endcase
    end
end
endmodule
/*

// State definitions 
localparam [5:0] 
                    TX_STOP             = 6'b000000,
    TX_HS_REQUEST       = 6'b000001,     TX_LP_RQST          = 6'b001000,
    TX_HS_PREPARE       = 6'b000011,     TX_LP_YIELD         = 6'b001001,   
    TX_HS_PREAMBLE      = 6'b000010,     TX_TA_REQUEST       = 6'b001011,     TX_ESC_RQST         = 6'b011001,
    TX_HS_SEND_DATA     = 6'b000110,     TX_TA_GO            = 6'b001010,     TX_ESC_GO           = 6'b011011,
    TX_HS_SYNC_WORD     = 6'b000111,     RX_TA_LOOK          = 6'b001110,     TX_ESC_CMD          = 6'b010011,
    TX_HS_SEND_DATA     = 6'b000110,     RX_TA_ACK           = 6'b001111,     TX_LPDT             = 6'b010010,    TX_TRIGGERS         = 6'b010001,    TX_ULPS             = 6'b33, 
    TX_HS_POST          = 6'b000100,     RX_STOP             = 6'b001101,     TX_LPDT_Pause       = 6'b110010,    TX_MARK             = 6'b010000,    TX_MARK             = 6'b010000,
    TX_STOP             = 6'b000000,                                          TX_MARK             = 6'b010000,    TX_STOP             = 6'b000000,     TX_STOP            = 6'b000000,
                                                                              TX_STOP             = 6'b000000,




                                    RX_STOP             = 6'b001101,
                                    RX_LP_RQST          = 6'b101101,
                                    RX_LP_YIELD         = 6'b101100,    RX_LP_YIELD         = 6'b101100,
                                    RX_TA_RQST          = 6'b100100,    RX_ESC_RQST         = 6'b000000,
                                    RX_TA_WAIT          = 6'b100101,    RX_Esc_Go           = 6'b100111,
                                    TX_TA_GET           = 6'b100001,    RX_ESC_CMD          = 6'b101111,                                          
                                    TX_TA_ACK           = 6'b100000,    RX_LPDT             = 6'b101101,        RX_ULPS             = 6'b24,      RX_WAIT             = 6'b27,
                                    TX_STOP             = 6'b000000,    RX_STOP             = 6'b001101,        RX_ULPS_T_WAKE_UP   = 6'b25,      RX_STOP             = 6'b001101,
                                                                                                                RX_WAIT             = 6'b27,
                                                                                                                RX_STOP             = 6'b001101,
    
    
    
    
    FORCE_RX            = 6'b28,
     
     
      
      
     */
    
    
