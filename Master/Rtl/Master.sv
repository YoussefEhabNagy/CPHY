module Master(
    ////////////////////////// TX Inputs //////////////////////
    input          RstN,
    input          TxSymbolClkHS,
    input          TxWordClkHs,
    //High Speed
    input   [15:0] TxDataHS,
    input          TxSendSyncHS,
    input          TxReqHS,

    //Escape Mode
    //TX
    input          TxClkEsc,
    input          TxReqEsc,
    input          TxLpdtEsc,
    input          TxUlpsEsc,
    input          TxUlpsExit,
    input   [3:0]  TxTriggerEsc,
    input   [7:0]  TxDataEsc,
    input          TxValidEsc,
    input   [2:0]  LpRx,        // A B C

    //Control Signals
    input          TurnRequest,
    input          TurnDisable,
    input          ForceRxmode,
    input          ForceTxStopmode,
    input          Enable, // Enable Lane Module

    //Contetion detection
    input          LP_CD_A,
    input          LP_CD_B,
    input          LP_CD_C,

    ////////////////////////// TX outputs //////////////////////
    output [7:0] A,
    output [7:0] B,
    output [7:0] C,

    //High speed
    output         TxReadyHS,

    //Escape Mode
    //TX
    output         TxReadyEsc,

    // Control and Status Outputs
    output wire        Direction,       // Bus direction (1=RX, 0=TX)
    output wire        Stopstate,       // Stop state indicator
    output wire        UlpsActiveNot,   // Ultra-low power active (inverted)

    //Contention Signals 
    output wire    ErrContentionLP0,
    output wire    ErrContentionLP1,
   ////////////////////////// RX outputs //////////////////////
    // LP/Escape Mode Outputs
    output wire [7:0]  RxEscData,       // Escape mode parallel data output
    output wire        LpRxEn,
    output wire        RxClkEsc,        // Escape mode clock output
    output wire        RxValidEsc,      // Escape mode data valid
    output wire [3:0]  RxTriggerEsc,    // Escape mode trigger signals
    output wire        RxUlpsEsc,       // Escape mode ultra-low power state
    output wire        RxLpdtEsc,       // Escape mode low-power data transfer
    // Error Outputs
    output wire        ErrEsc,          // Escape mode error
    output wire        ErrSyncEsc,      // Escape mode sync error
    output wire        ErrControl,      // Escape mode control error
    output wire        ErrSotHS,        // High-speed start of transmission error
    output wire        ErrSotSyncHS     // High-speed sync error
    
);
   ////////////////////////// TX Internal wires //////////////////////
    wire [1:0]   A_PU_PD; //HS_Encoder OUT A
    wire [1:0]   B_PU_PD; //HS_Encoder OUT B
    wire [1:0]   C_PU_PD; //HS_Encoder OUT C
    wire         HsTxEn;
    wire [2:0]   LpTx;
    wire         LpTxEn;
    //mapper
    wire [15:0] TxData;
    wire [6:0]  TxRotation;
    wire [6:0]  TxPolarity;
    wire [6:0]  TxFlip;

    //HS_Serializer
    wire        HsSerializerEn;
    wire [2:0]  SerSym;

    //HS_Sequencer
    wire        TxRequestHSSEQ;
    wire [2:0]  HsSeqCtr;
    wire        SeqDone;
    wire [2:0]  SeqSym;

    //SerSeqMux
    wire        SerSeqSel;
    wire [2:0]  Sym;

    //Esc_Sequencer
    wire        SeqBit;
    wire        CmdDone;
    wire [7:0]  EscSeqCtr;

    //ESC_Serializer
    wire        EscSerEn;
    wire        SerBit;
    wire        SerReadyEsc;
    wire        SerLastBit;
    wire        Pause_Ready;

    //EscSerSeqMux
    wire        EscSerSeqSel;
    wire        EscBitEncoder;

    //EscEncoder
    wire        EscEncoderEn;
    wire        EscEncoderDataValid;
    wire        EscEncoderA;
    wire        EscEncoderB;
    wire        EscEncoderC;

    //Encoder
    wire        EncoderEn;

    //TX_Ctrl_Logic
    wire        TXCtrlLogicA;
    wire        TXCtrlLogicB;
    wire        TXCtrlLogicC;
    wire [1:0]  TXCtrlOut;

    //Mux_A-Mux_B-Mux_C
    wire        LpCtrEscSel;

   ///FSM 
    wire        InErrEsc ;
    wire        InRxInvalidCodeHS; // High-speed invalid code flag
    wire        InErrSotHS;        // Start of transmission error flag from Sequence_Detector
    wire        InErrSotSyncHS;    // Start of transmission sync error from Sequence_Detector

  ////////////////////////// RX Internal wires //////////////////////
  //clock recovery lp
    wire         RxClkEscOut;     // Escape mode clock

    //Esc Decoder
    wire        EscDecoderEn;      
    wire        InRxLpdtEsc;      // Low-power data transfer flag
    wire        InRxUlpsEsc;      // Ultra-low power state flag
    wire [3:0]  InRxTriggerEsc;   // Escape mode trigger signals
    wire        EscBitDecodr;     // Escape bit from Esc_Decoder
    wire        LpFsmStop;        // Low-power state machine stop signal

    //Esc-Deserializer
    wire        EscDeserEn;             // Escape deserializer enable

    //RXCtrl_Decoder
    wire [1:0]  CtrlDecoderOut; 
    wire        CtrlDecoderEn;
    

//=======================================================================================================
// NEW SYNC: Added Synchronization Wires
//=======================================================================================================


    // RX Domain Synchronization //

    // FSM Input Synchronization
    wire       LpFsmStop_sync;
    wire [1:0] CtrlDecoderOut_sync;
    wire [3:0] InRxTriggerEsc_sync;
    wire       InRxUlpsEsc_sync;
    wire       InRxLpdtEsc_sync;
    wire       InErrEsc_sync;
    wire       InErrControl_sync;
    wire [3:0] DetectedSeq_sync;
    wire       InRxInvalidCodeHS_sync;
    wire       InErrSotHS_sync;
    wire       InErrSotSyncHS_sync;

    // FSM Output Synchronization
    wire       EscDecoderEn_sync;
    wire       EscDeserEn_sync;
    wire       RequestDetection_sync;

    // TX Domain Synchronization //
    wire        TxSendSyncHSSync;
    wire        TxReqHSSync;
    wire        TxReqEscSync;
    wire        TxLpdtEscSync;
    wire        TxUlpsEscSync;
    wire        TxUlpsExitSync;
    wire  [3:0] TxTriggerEscSync;
    wire        TxValidEscSync;
    wire        TurnRequestSync;//
    wire        TurnDisableSync;//
    wire        ForceRxmodeSync;//
    wire        ForceTxStopmodeSync;//
    wire        SeqDoneSync;
    wire        CmdDoneSync; 
    wire        SerReadyEscSync; 
    wire        SerLastBitSync; 
    wire        HsSeqEnSync;
    wire        HsSerializerEnSync; 
    wire        EncoderEnSync; 
    wire        EscBitEncoderSync; //
    wire        EscSerSeqSelSync;
    wire        EscSerEnSync;
    wire        SerSeqSelSync;
    wire        EscEncoderEnSync;
    wire        EscEncoderDataValidSync;
    wire        TxRequestHSSEQSync;
    wire [2:0]  HsSeqCtrSync;
    wire [7:0]  EscSeqCtrSync;//


  ////////////////////////// TX Instantiate Modules //////////////////////
    Master_Analog_Model Master_Analog_Model_U0(
    .A_PU_PD(A_PU_PD),
    .B_PU_PD(B_PU_PD),
    .C_PU_PD(C_PU_PD),
    .HsTxEn(HsTxEn),
    .LpTx(LpTx),
    .LpTxEn(LpTxEn),
    .LpRx(LpRx),
    .A(A),
    .B(B),
    .C(C)
);

    mapper mapper_U0 (
        .TxData       (TxDataHS),
        .TxRotation   (TxRotation),
        .TxPolarity   (TxPolarity),
        .TxFlip       (TxFlip)
    );

    HS_Serializer HS_Serializer_U0 (
        .TxSymbolClkHS   (TxSymbolClkHS),
        .RstN            (RstN_SymClk),
        .TxFlip          (TxFlip),
        .TxRotation      (TxRotation),
        .TxPolarity      (TxPolarity),
        .HsSerializerEn  (HsSerializerEn),
        .SerSym          (SerSym)
    );

    HS_Sequencer HS_Sequencer_U0 (
        .RstN           (RstN_SymClk),
        .TxSymbolClkHS  (TxSymbolClkHS),
        .SeqDone        (SeqDone),
        .HsSeqCtr       (HsSeqCtr),
        .TxReqHS        (TxRequestHSSEQ),
        .SeqSym         (SeqSym)
    );

    Mux_3Bit SerSeqMux (
        .SeqSym         (SeqSym),
        .SerSym         (SerSym),
        .SerSeqSel      (SerSeqSel),
        .Sym            (Sym)
    );

    Esc_Sequencer Esc_Sequencer_U0 (
        .RstN           (RstN_EscClk),
        .TxClkEsc       (TxClkEsc),
        .EscSeqCtr      (EscSeqCtrSync),
        .SeqBit         (SeqBit),
        .CmdDone        (CmdDone)
    );

    ESC_Serializer ESC_Serializerr_U0 (
        .TxClkEsc       (TxClkEsc),
        .RstN           (RstN_EscClk),
        .TxDataEsc      (TxDataEsc),
        .EscSerEn       (EscSerEnSync),
        .TxReadyEsc     (SerReadyEsc),
        .LastBit        (SerLastBit),
        .SerBit         (SerBit),
        .Pause_Ready    (Pause_Ready)
    );

    //Delay the selector 1 cycle for synchronization allignment
    reg Delayed_EscSerSeqSelSync;
    reg Delayed_DV;
    always @(posedge TxClkEsc, negedge RstN_EscClk) begin
        if(!RstN_EscClk) begin
            Delayed_EscSerSeqSelSync <= 0;
            Delayed_DV <= 0;
        end
        else begin
            Delayed_EscSerSeqSelSync <= EscSerSeqSelSync;
            Delayed_DV <= EscEncoderDataValidSync;
        end
    end

    Mux_1Bit EscSerSeqMux (
        .A              (SeqBit),
        .B              (SerBit),
        .Sel            (Delayed_EscSerSeqSelSync),
        .Out            (EscBitEncoder)///////
    );

    Esc_Encoder EscEncoder_U0 (
        .RstN           (RstN_EscClk),
        .TxClkEsc       (TxClkEsc),
        .EscBit         (EscBitEncoder),
        .EscEncoderEn   (EscEncoderEnSync),
        .DataValid      (Delayed_DV),
        .A              (EscEncoderA),
        .B              (EscEncoderB),
        .C              (EscEncoderC)
    );

    Encoder HS_Encoder_U0 (
        .RstN           (RstN_SymClk),
        .EncoderEn      (EncoderEn),
        .TxSymbolClkHS  (TxSymbolClkHS),
        .Sym            (Sym),
        .A              (A_PU_PD),
        .B              (B_PU_PD),
        .C              (C_PU_PD)
    );

    TX_Ctrl_Logic TX_Ctrl_Logic_U0 (
        .TxCtrlOut      (TXCtrlOut),
        .A              (TXCtrlLogicA),
        .B              (TXCtrlLogicB),
        .C              (TXCtrlLogicC)
    );

    Mux_1Bit Mux_A_LP_TX (
        .A              (TXCtrlLogicA),
        .B              (EscEncoderA),
        .Sel            (LpCtrEscSel),
        .Out            (LpTx[2])
    );

    Mux_1Bit Mux_B_LP_TX (
        .A              (TXCtrlLogicB),
        .B              (EscEncoderB),
        .Sel            (LpCtrEscSel),
        .Out            (LpTx[1])
    );

    Mux_1Bit Mux_C_LP_TX (
        .A              (TXCtrlLogicC),
        .B              (EscEncoderC),
        .Sel            (LpCtrEscSel),
        .Out            (LpTx[0])
    );

    ContentionDetection contention_detection_U0 (
        .LpCdA              (LP_CD_A),
        .LpCdB              (LP_CD_B),
        .LpCdC              (LP_CD_C),
        .LpTxA              (LpTx[2]),
        .LpTxB              (LpTx[1]),
        .LpTxC              (LpTx[0]),
        .LpRxA              (LpRx[2]),
        .LpRxB              (LpRx[1]),
        .LpRxC              (LpRx[0]),
        .ErrContentionP0    (ErrContentionLP0),
        .ErrContentionP1    (ErrContentionLP1)
    );
	


 cphy_tx_fsm cphy_tx_fsm_U0 (
        .TxWordClkHS         (TxWordClkHs),
        .RstN                (RstN_WordClk),
        .TurnRequest         (TurnRequestSync),
        .TxReqEsc            (TxReqEscSync),
        .TxReqHS             (TxReqHS),
        .TxUlpsEsc           (TxUlpsEscSync),
        .TxLpdtEsc           (TxLpdtEscSync),
        .TxUlpsExit          (TxUlpsExitSync),
        .TxTriggerEsc        (TxTriggerEscSync),
        .SeqDone             (SeqDone),///////
        .CmdDone             (CmdDoneSync),///
        .TxSendSyncHS        (TxSendSyncHS),
        .ForceRxmode         (ForceRxmodeSync),
        .ForceTxStopmode     (ForceTxStopmodeSync),
        .TurnDisable         (TurnDisableSync),
        .Enable              (Enable),
        .TxValidEsc          (TxValidEscSync),
        .SerReadyEsc         (SerReadyEscSync),///
        .SerLastBit          (SerLastBitSync),///
        .HsSerializerEn      (HsSerializerEn),//
        .SerSeqSel           (SerSeqSel),///////////////
        .EncoderEn           (EncoderEn),//
        .TxReadyHS           (TxReadyHS),
        .TxReadyEsc          (TxReadyEsc),
        .Direction           (Direction),
        .Stopstate           (Stopstate),
        .EscSerEn            (EscSerEn),//
        .EscSerSeqSel        (EscSerSeqSel),
        .EscEncoderEn        (EscEncoderEn),//
        .EscSeqCtr           (EscSeqCtr),
        .TxCtrlOut           (TXCtrlOut),
        .LpCtrlEscSel        (LpCtrEscSel),
        .LpTxEn              (LpTxEn),
        .HsTxEn              (HsTxEn),
        .HsSeqCtr            (HsSeqCtr),
        .UlpsActiveNot       (UlpsActiveNot),
        .TxRequestHSSEQ      (TxRequestHSSEQ),//
        .EscEncoderDataValid (EscEncoderDataValid),////////
        .Pause_Ready         (Pause_Ready),

/////////////////////////////////RX///////////////////////
		// Inputs 	
        .LpCLK(RxClkEscOut),                                
        .LpFsmStop(LpFsmStop_sync),
        .LpState  (CtrlDecoderOut_sync),                                          
        .InRxTriggerEsc(InRxTriggerEsc_sync),
        .InRxUlpsEsc(InRxUlpsEsc_sync),
        .InRxLpdtEsc(InRxLpdtEsc_sync),
        .InErrEsc(InErrEsc_sync),
         //OUTPUTS          
        .RequestDetection(RequestDetection),
        .LpRxEn             (LpRxEn),
        .EscDecoderEn       (EscDecoderEn),
        .CtrlDecoderEn      (CtrlDecoderEn),
		.RxClkEsc(RxClkEsc)
    );

  //////////////////////////RX Instantiate Modules //////////////////////
 
	//=======================================
	//=============== LP RX =================
	//=======================================
	
    // Clock Recovery (LP)
    Clock_Recovery_LP clk_recovery_lp (
        .A(LpRx[2]),
        .C(LpRx[0]),
        .RxClkEsc(RxClkEscOut)
    );
    
    // ESC Decoder
    Esc_Decoder esc_decoder (
        .RxClkEsc(RxClkEscOut),
        .RST(RstN_RxEscClk),
        .EscDecoderEn(EscDecoderEn_sync),
        .A(LpRx[2]),
        .B(LpRx[1]),
        .C(LpRx[0]),
        .RequestDetection(RequestDetection_sync),
        .RxLpdtEsc(RxLpdtEsc),
        .RxUlpsEsc(RxUlpsEsc),
        .RxTriggerEsc(RxTriggerEsc),
        .EscBit(EscBit),
        .ErrControl(ErrControl),
        .ErrSyncEsc(ErrSyncEsc),
        .ErrEsc(ErrEsc),
        .LpFsmStop(LpFsmStop),
        .EscDeserEn(EscDeserEn)
    );
        
    // ESC Deserializer
    ESC_Deserializer esc_deserializer (
        .RxClkEsc(RxClkEscOut),
        .RstN(RstN_RxEscClk),
        .SerBit(EscBit),
        .EscDeserEn(EscDeserEn),
        .RxValidEsc(RxValidEsc),                                         
        .RxEscData(RxEscData)
    );

    // Control Decoder
    Rx_Ctrl_Decoder rx_ctrl_decoder (
        .A(LpRx[2]),
        .B(LpRx[1]),
        .C(LpRx[0]),
        .CtrlDecoderEn(CtrlDecoderEn),
        .CtrlDecoderOut(CtrlDecoderOut)
    );
    

//=======================================================================================================
// sync_levels
//=======================================================================================================

    
   sync_level #(1) sync_EscDecoderEn      (.clk_dst(RxClkEscOut),   .RstN(RstN_RxEscClk), .async_in(EscDecoderEn),     .sync_out(EscDecoderEn_sync));
   sync_level #(1) sync_RequestDetection  (.clk_dst(RxClkEscOut),   .RstN(RstN_RxEscClk), .async_in(RequestDetection), .sync_out(RequestDetection_sync));

   sync_level #(2) sync_CtrlDecoderOut 
   (.clk_dst(TxWordClkHs), .RstN(RstN), .async_in(CtrlDecoderOut),  .sync_out(CtrlDecoderOut_sync));
   sync_level #(1) sync_LpFsmStop                                   
   (.clk_dst(TxWordClkHs), .RstN(RstN), .async_in(LpFsmStop),       .sync_out(LpFsmStop_sync));
   sync_level #(4) sync_InRxTriggerEsc                              
   (.clk_dst(TxWordClkHs), .RstN(RstN), .async_in(RxTriggerEsc),    .sync_out(InRxTriggerEsc_sync));
   sync_level #(1) sync_InRxUlpsEsc                                 
   (.clk_dst(TxWordClkHs), .RstN(RstN), .async_in(RxUlpsEsc),       .sync_out(InRxUlpsEsc_sync));
   sync_level #(1) sync_InRxLpdtEsc                                 
   (.clk_dst(TxWordClkHs), .RstN(RstN), .async_in(RxLpdtEsc),       .sync_out(InRxLpdtEsc_sync));
   sync_level #(1) sync_InErrEsc       
   (.clk_dst(TxWordClkHs), .RstN(RstN), .async_in(ErrEsc),          .sync_out(InErrEsc_sync));
    

   sync_level sync_level_U0 (
        .clk_dst      (TxWordClkHs),
        .RstN         (RstN),
        .async_in     (SerReadyEsc),
        .sync_out     (SerReadyEscSync)
    );

   sync_level sync_level_U1 (
        .clk_dst      (TxWordClkHs),
        .RstN         (RstN),
        .async_in     (CmdDone),
        .sync_out     (CmdDoneSync)
    );
    
   sync_level sync_level_U2 (
        .clk_dst      (TxClkEsc),
        .RstN         (RstN_EscClk),
        .async_in     (EscEncoderDataValid),
        .sync_out     (EscEncoderDataValidSync)
    );

   sync_level sync_level_U3 (
        .clk_dst      (TxWordClkHs),
        .RstN         (RstN),
        .async_in     (SerLastBit),
        .sync_out     (SerLastBitSync)
    );
    
   sync_level sync_level_U4 (
        .clk_dst  (TxWordClkHs),
        .RstN     (RstN),
        .async_in (ForceTxStopmode),
        .sync_out (ForceTxStopmodeSync)
    );


   sync_level sync_level_U5 (
        .clk_dst      (TxSymbolClkHS),
        .RstN         (RstN_SymClk),
        .async_in     (HsSerializerEn),
        .sync_out     (HsSerializerEnSync)
    );

   sync_level sync_level_U6 (
        .clk_dst      (TxSymbolClkHS),
        .RstN         (RstN_SymClk),
        .async_in     (EncoderEn),
        .sync_out     (EncoderEnSync)
    );

   sync_level sync_level_U8 (
        .clk_dst      (TxClkEsc),
        .RstN         (RstN_EscClk),
        .async_in     (EscSerEn),
        .sync_out     (EscSerEnSync)
    );

   sync_level sync_level_U9 (
        .clk_dst      (TxClkEsc),
        .RstN         (RstN_EscClk),
        .async_in     (EscEncoderEn),
        .sync_out     (EscEncoderEnSync)
    );

   sync_level sync_level_U10 (
        .clk_dst      (TxWordClkHs),
        .RstN         (RstN),
        .async_in     (SeqDone),
        .sync_out     (SeqDoneSync)
    );

   sync_level sync_level_U11 (
        .clk_dst      (TxSymbolClkHS),
        .RstN         (RstN_SymClk),
        .async_in     (SerSeqSel),
        .sync_out     (SerSeqSelSync)
    );

   sync_level sync_level_U12 (
        .clk_dst      (TxClkEsc),
        .RstN         (RstN_EscClk),
        .async_in     (EscSerSeqSel),
        .sync_out     (EscSerSeqSelSync)
    );

   sync_level #(3) sync_level_U13 (
        .clk_dst      (TxSymbolClkHS),
        .RstN         (RstN_SymClk),
        .async_in     (HsSeqCtr),
        .sync_out     (HsSeqCtrSync)
    );

   sync_level #(8) sync_level_U14 (
        .clk_dst      (TxClkEsc),
        .RstN         (RstN_EscClk),
        .async_in     (EscSeqCtr),
        .sync_out     (EscSeqCtrSync)
    );

   sync_level sync_level_U15 (
        .clk_dst  (TxWordClkHs),
        .RstN     (RstN),
        .async_in (TxSendSyncHS),
        .sync_out (TxSendSyncHSSync)
    );
    
   sync_level sync_level_U16 (
        .clk_dst  (TxWordClkHs),
        .RstN     (RstN),
        .async_in (TxReqHS),
        .sync_out (TxReqHSSync)
    );
    
   sync_level sync_level_U17 (
        .clk_dst  (TxWordClkHs),
        .RstN     (RstN),
        .async_in (TxReqEsc),
        .sync_out (TxReqEscSync)
    );
    
   sync_level sync_level_U18 (
        .clk_dst  (TxWordClkHs),
        .RstN     (RstN),
        .async_in (TxLpdtEsc),
        .sync_out (TxLpdtEscSync)
    );
    
   sync_level sync_level_U19 (
        .clk_dst  (TxWordClkHs),
        .RstN     (RstN),
        .async_in (TxUlpsEsc),
        .sync_out (TxUlpsEscSync)
    );
    
   sync_level sync_level_U20 (
        .clk_dst  (TxWordClkHs),
        .RstN     (RstN),
        .async_in (TxUlpsExit),
        .sync_out (TxUlpsExitSync)
    );
    
   sync_level #(4) sync_level_U21 (
        .clk_dst  (TxWordClkHs),
        .RstN     (RstN),
        .async_in (TxTriggerEsc),
        .sync_out (TxTriggerEscSync)
    );
    
   sync_level sync_level_U22 (
        .clk_dst  (TxWordClkHs),
        .RstN     (RstN),
        .async_in (TxValidEsc),
        .sync_out (TxValidEscSync)
    );
    
   sync_level sync_level_U23 (
        .clk_dst  (TxWordClkHs),
        .RstN     (RstN),
        .async_in (TurnRequest),
        .sync_out (TurnRequestSync)
    );
    
   sync_level sync_level_U24 (
        .clk_dst  (TxWordClkHs),
        .RstN     (RstN),
        .async_in (TurnDisable),
        .sync_out (TurnDisableSync)
    );
    
   sync_level sync_level_U25 (
        .clk_dst  (TxWordClkHs),
        .RstN     (RstN),
        .async_in (ForceRxmode),
        .sync_out (ForceRxmodeSync)
    );

   sync_level sync_level_U26 (
        .clk_dst  (TxSymbolClkHS),
        .RstN     (RstN_SymClk),
        .async_in (TxRequestHSSEQ),
        .sync_out (TxRequestHSSEQSync)
    );

   sync_level sync_level_U27 (
        .clk_dst  (TxSymbolClkHS),
        .RstN     (RstN_SymClk),
        .async_in (TxReadyHSSync),
        .sync_out (TxReadyHS)
    );
    
    Reset_Sync Reset_Sync_SymClk(
        .clk(TxSymbolClkHS),
        .RstN(RstN),
        .sync_out(RstN_SymClk)
    );

    Reset_Sync Reset_Sync_WordClk(
        .clk(TxWordClkHs),
        .RstN(RstN),
        .sync_out(RstN_WordClk)
    );

    Reset_Sync Reset_Sync_EscClk(
        .clk(TxClkEsc),
        .RstN(RstN),
        .sync_out(RstN_EscClk)
    );
    
    Reset_Sync Reset_Sync_RxEscClk(
        .clk(RxClkEscOut),
        .RstN(RstN),
        .sync_out(RstN_RxEscClk)
    );


endmodule