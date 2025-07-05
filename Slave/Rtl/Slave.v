//=================================================================================================
//  File Name    : slave.v
//  Description  : 
//      This module implements the C-PHY Slave interface handling both High-Speed (HS) and 
//      Low-Power / Escape (LP/Esc) modes of operation according to the C-PHY protocol specification.
//      It manages the reception of C-PHY differential signals (A, B, C) and recovers clocks and data
//      for both HS and LP modes, coordinating decoders, deserializers, sequence detectors, and FSM control.
//
//      The module supports the full C-PHY RX data path, including clock recovery for HS and LP,
//      symbol decoding, data deserialization, and escape sequence processing. It integrates 
//      multiple submodules for decoding, deserialization, error detection, and RX/TX mode 
//      switching with tight control through the embedded SlaveFSM.
//
//      Control inputs allow forcing RX mode, disabling turn-around, forcing TX stop mode, 
//      and enabling/disabling the slave module. Status outputs indicate valid data, errors, 
//      and mode states to the higher protocol layers.
//
//      This design targets robust and accurate implementation of C-PHY slave receiver logic,
//      ensuring protocol compliance for serial data reception and response in automotive 
//      and high-speed camera interface applications.
//
//  Key Inputs    : 
//      - A, B, C            : C-PHY differential signals inputs
//      - RxClkFsm           : FSM clock input
//      - RstN               : Active-low reset
//      - ForceRxmode        : Force receiver mode
//      - TurnDisable        : Disable turn-around sequence
//      - TurnRequest        : Request to turn around direction
//      - ForceTxStopmode    : Force TX stop mode
//      - Enable             : Module enable signal
//      - TxClkEsc, TxReqEsc, TxLpdtEsc, TxUlpsEsc, TxUlpsExit, TxTriggerEsc, TxValidEsc, CmdDone : TX Escape signals
//
//  Key Outputs   : 
//      - RxDataHS           : High-speed data output
//      - RxValidHS, RxActiveHS, RxSyncHS : High-speed data status flags
//      - RxInvalidCodeHS    : High-speed invalid code flag
//      - HsRxEn             : High-speed RX enable
//      - RxEscData          : Escape mode data output
//      - LpRxEn, RxClkEsc, RxValidEsc, RxTriggerEsc, RxUlpsEsc, RxLpdtEsc : LP/Escape mode control and data signals
//      - LpTxEn, LpCtrEscSel, EscSeqCtr, EscSeqEn, EscSerEn, EscSerSeqSel, EscEncoderEn : Turn-around and Escape mode TX controls
//      - DataValid           : Data valid indication
//      - TxCtrlOut, TxReadyEsc : TX control outputs
//      - Direction, Stopstate, UlpsActiveNot : Bus state signals
//      - ErrEsc, ErrSyncEsc, ErrControl, ErrSotHS, ErrSotSyncHS : Error status outputs
//
//  Author       : Ahmed
//  Date         : 19/5/2025
//=================================================================================================

`timescale 1ns / 1ps

module slave (
    // Primary Inputs
    input  wire        A,               // C-PHY input signal A
    input  wire        B,               // C-PHY input signal B
    input  wire        C,               // C-PHY input signal C
    input  wire        RxClkFsm,        
    input  wire        RstN,            // Active-low reset
    //============ PPI Control Signals =================================
    input  wire        ForceRxmode,     // Force RX mode signal
    input  wire        TurnDisable,     // Disable turning signal
    input  wire        TurnRequest,     // Request to turn signal
    input  wire        ForceTxStopmode, // Force TX stop mode signal
    input  wire        Enable,          // Enable signal
    //============ TX Signals =================================
    input  wire        TxClkEsc,        // Escape mode clock (assumed external or tied off)
    input  wire        TxReqEsc,        // Escape mode request (assumed external or tied off)
    input  wire        TxLpdtEsc,       // Escape mode low-power data transfer (assumed external or tied off)
    input  wire        TxUlpsEsc,       // Escape mode ultra low-power Request
    input  wire        TxUlpsExit,      // Escape mode ultra low-power Exit
    input  wire [3:0]  TxTriggerEsc,    // Escape mode trigger signals (assumed external or tied off)
    input  wire [7:0]  TxDataEsc,
    input  wire        TxValidEsc,      // Escape mode data valid (assumed external or tied off)
    
    //contention detection
    input  wire        LP_CD_A,
    input  wire        LP_CD_B,
    input  wire        LP_CD_C,

    // HS Mode Outputs
    output wire [15:0] RxDataHS,        // High-speed parallel data output
    output wire        RxValidHS,       // High-speed data valid
    output wire        RxActiveHS,      // High-speed active
    output wire        RxSyncHS,        // High-speed sync detected
    output wire        RxInvalidCodeHS, // High-speed invalid code flag
    output wire        HsRxEn,          // High-speed RX enable

    // LP/Escape Mode Outputs
    output wire [7:0]  RxEscData,       // Escape mode parallel data output
    output wire        LpRxEn,
    output wire        RxClkEsc,        // Escape mode clock output
    output wire        RxValidEsc,      // Escape mode data valid
    output wire [3:0]  RxTriggerEsc,    // Escape mode trigger signals
    output wire        RxUlpsEsc,       // Escape mode ultra-low power state
    output wire        RxLpdtEsc,       // Escape mode low-power data transfer

    // Control and Status Outputs
    output wire        Direction,       // Bus direction (1=RX, 0=TX)
    output wire        Stopstate,       // Stop state indicator
    output wire        UlpsActiveNot,   // Ultra-low power active (inverted)

    // Error Outputs
    output wire        ErrEsc,          // Escape mode error
    output wire        ErrSyncEsc,      // Escape mode sync error
    output wire        ErrControl,      // Escape mode control error
    output wire        ErrSotHS,        // High-speed start of transmission error
    output wire        ErrSotSyncHS,     // High-speed sync error
    
    //TX
    output wire        TxReadyEsc,
    output wire  [2:0] LpTx,
    output wire        LpTxEn,
    ///   -----------------------------      thabota   --------------------------------------------------
    input wire RecoveredClk,       // input to clk gating
    output wire  RxWordClkHS_out,     // out clk from fsm

    //Contention Error Signals 
    output wire        ErrContentionLP0,
    output wire        ErrContentionLP1
    
);  
    

//======================================================================================================
//================================================= RX =================================================
//======================================================================================================
    // Internal Wires
    // Control Signals from RxFSM
    //thabota edits 
    //clock hs recovery
    wire        RxSymClkHS;       // High-speed symbol clock
    wire [3:0]  DetectedSeq;      // Sequence detector output
    reg  [3:0]  DetectedSeq_REG;      // Sequence detector output
    reg  [3:0]  DetectedSeqREG;      // Sequence detector output
    wire        RxWordClkHS;      // High-speed word clock (assumed external or derived)
    wire        HsFsmEn;
    wire        SettleExp;
   // wire        RecoveredClkHS;
    // Hs-decoder
    wire        HsDecoderEn;
    wire [2:0]  RxSymbol;         // Symbol output from Decoder
    wire [2:0]  InRxSymbol;         // Symbol output from Decoder
    // HS-Deserializer
    wire        HSDeserEn;        // High-speed deserializer enable   
    wire [6:0]  RxPolarity;       // Polarity bits from HS_Deserializer
    wire [6:0]  InRxPolarity ;
    wire [6:0]  RxRotation;       // Rotation bits from HS_Deserializer
    wire [6:0]  InRxRotation;       // Rotation bits from HS_Deserializer
    wire [6:0]  RxFlip;           // Flip bits from HS_Deserializer
    wire [6:0]  InRxFlip;           // Flip bits from HS_Deserializer

    //Seq Detector
    wire        HsSeqDetectorEn;  // High-speed sequence detector enable

    //ctrl decoder
    wire        CtrlDecoderEn;    // Control decoder enable
    wire [1:0]  CtrlDecoderOut;   // Control decoder output

    //clock recovery lp
    wire         RxClkEscOut;     // Escape mode clock

    //�?Esc Decoder
    wire        EscDecoderEn;      
    wire        InRxLpdtEsc;      // Low-power data transfer flag
    wire        InRxUlpsEsc;      // Ultra-low power state flag
    wire [3:0]  InRxTriggerEsc;   // Escape mode trigger signals
    wire        EscBit;           // Escape bit from Esc_Decoder
    wire        InRxValidEsc;     // Escape mode data valid
    wire        LpFsmStop;        // Low-power state machine stop signal

    //Esc-Deserializer
    wire        EscDeserEn;             // Escape deserializer enable

    // FSm
    wire        HsSettleExp ;
    wire        InErrEsc ;
    wire        InErrSyncEsc;      // Escape mode sync error
    wire        InErrControl;      // Control error
    wire        InRxInvalidCodeHS; // High-speed invalid code flag
    wire        InErrSotHS;        // Start of transmission error flag from Sequence_Detector
    wire        InErrSotSyncHS;    // Start of transmission sync error from Sequence_Detector

    //Flags
    wire        RequestDetection;    // This flag to know that the Slave received Request from the Master
    
    
//=======================================================================================================
// NEW SYNC: Added Synchronization Wires
//=======================================================================================================

    // FSM Input Synchronization
    // RX Domain Synchronization
    wire       LpFsmStop_sync;
    wire [1:0] CtrlDecoderOut_sync;
    wire       InRxValidEsc_sync;
    wire [3:0] InRxTriggerEsc_sync;
    wire       InRxUlpsEsc_sync;
    wire       InRxLpdtEsc_sync;
    wire       InErrEsc_sync;
    wire       InErrSyncEsc_sync;
    wire       InErrControl_sync;
    wire [3:0] DetectedSeq_sync;
    wire       InRxInvalidCodeHS_sync;
    wire       InErrSotHS_sync;
    wire       InErrSotSyncHS_sync;
        
    // TX Domain Synchronization
    wire       TxReqEsc_sync;
    wire       TxValidEsc_sync;
    wire       TxUlpsEsc_sync  ;
    wire       TxLpdtEsc_sync  ;
    wire       TxUlpsExit_sync ;
    wire       CmdDone_sync    ;
    wire       SerReadyEsc_sync;
    wire       SerLastBit_sync ;
    wire [3:0] TxTriggerEsc_sync;
    
    // FSM Output Synchronization
    // RX Domain Synchronization
    wire       HsSettleExp_sync;
    wire       HsDecoderEn_sync;
    wire       HSDeserEn_sync;
    wire       HsSeqDetectorEn_sync;
    wire       EscDecoderEn_sync;
    wire       EscDeserEn_sync;
    wire       RequestDetection_sync;
    
    // TX Domain Synchronization
    wire       EscSeqEn_sync;
    wire       EscSerEn_sync;
    wire       EscSerSeqEn_sync;
    wire       EscEncoderEn_sync;
    wire [2:0]    EscSeqCtr_sync;
    wire  [1:0]     TxCtrlOut_sync;
    wire       EscEncoderDataValid_sync;
	
	
	

//=======================================================================================================
// RX Path with Synchronizers
//=======================================================================================================

    synchronizer #(1) sync_HsSettleExp       (.clk(RecoveredClk),  .rst_n(RstN), .data_in(HsSettleExp),      .data_out(HsSettleExp_sync));
    synchronizer #(1) sync_HsDecoderEn       (.clk(RxSymClkHS),    .rst_n(RstN), .data_in(HsDecoderEn),      .data_out(HsDecoderEn_sync));
    synchronizer #(1) sync_HSDeserEn         (.clk(RxSymClkHS),    .rst_n(RstN), .data_in(HSDeserEn),        .data_out(HSDeserEn_sync));
    synchronizer #(1) sync_HsSeqDetectorEn   (.clk(RxSymClkHS),    .rst_n(RstN), .data_in(HsSeqDetectorEn),  .data_out(HsSeqDetectorEn_sync));
    synchronizer #(1) sync_EscDecoderEn      (.clk(RxClkEscOut),   .rst_n(RstN), .data_in(EscDecoderEn),     .data_out(EscDecoderEn_sync));
    synchronizer #(1) sync_EscDeserEn        (.clk(RxClkEscOut),   .rst_n(RstN), .data_in(EscDeserEn),       .data_out(EscDeserEn_sync));
    synchronizer #(1) sync_RequestDetection  (.clk(RxClkEscOut),   .rst_n(RstN), .data_in(RequestDetection), .data_out(RequestDetection_sync));

// Instantiate Modules
//Clock Recovery (HS)
   /* Clock_Recovery_HS clk_recovery_hs (
        .A(A),
        .B(B),
        .C(C),
        .RST(RstN),
        .RecoveredClk(RecoveredClkHS)
    ); */

    Clock_Gating clk_gating(
        .ClkIn(RecoveredClk),
        .Enable(HsSettleExp),
        .SymClk(RxSymClkHS)
    );

    Word_Clock_Gen wordclk(
        .SymClk(RxSymClkHS),
        .RST(RstN),
        .RxWordClkHs(RxWordClkHS)
	);

    // Clock Recovery (LP)
    Clock_Recovery_LP clk_recovery_lp (
        .A(A),
        .C(C),
        .RxClkEsc(RxClkEscOut)
    );

    // Decoder
    Decoder decoder (
        .reset(RstN),
        .DecoderEn(HsDecoderEn_sync),
        .RxSymbolClkHS(RxSymClkHS),
        .State({A, B, C}),
        .Sym(InRxSymbol)
    );

    //reg_file for Rxsymbol
    reg_file #(.width(3)) SymbolReg ( // Assuming RxSymbol is 3 bits wide
        .clk(RxSymClkHS),
        .rst_n(RstN),
        .data_in(InRxSymbol),
        .data_out(RxSymbol)
    );

    // HS Deserializer
    HS_Deserializer hs_deserializer (
        .RxSymClkHS(RxSymClkHS),
        .RstN(RstN),
        .SerSym(RxSymbol),
        .HSDeserEn(HSDeserEn_sync),
        .RxPolarity(InRxPolarity),
        .RxRotation(InRxRotation),
        .RxFlip(InRxFlip)
    );

    //reg_file for polarity
    reg_file PReg (
        .clk(RxSymClkHS),
        .rst_n(RstN),
        .data_in(InRxPolarity),
        .data_out(RxPolarity)
    );
    //reg_file for rotation
    reg_file RReg (
        .clk(RxSymClkHS),
        .rst_n(RstN),
        .data_in(InRxRotation),
        .data_out(RxRotation)
    );
    //reg_file for flip
    reg_file FReg (
        .clk(RxSymClkHS),
        .rst_n(RstN),
        .data_in(InRxFlip),
        .data_out(RxFlip)
    );

    // Demapper
    demapper demapper_inst (
        .clk(RxSymClkHS),
        .rst_n(RstN),
        .RxFlip(RxFlip),
        .RxRotation(RxRotation),
        .RxPolarity(RxPolarity),
        .RxDataHS(RxDataHS),
        .RxInvalidCodeHS(InRxInvalidCodeHS)
    );

    // ESC Deserializer
    ESC_Deserializer esc_deserializer (
        .RxClkEsc(RxClkEscOut),
        .RstN(RstN),
        .SerBit(EscBit),
        .EscDeserEn(EscDeserEn_sync),
        .RxValidEsc(InRxValidEsc),                                         
        .RxEscData(RxEscData)
    );

    // ESC Decoder
    Esc_Decoder esc_decoder (
        .RxClkEsc(RxClkEscOut),
        .RST(RstN),
        .EscDecoderEn(EscDecoderEn_sync),
        .A(A),
        .B(B),
        .C(C),
        .RequestDetection(RequestDetection),
        .RxLpdtEsc(InRxLpdtEsc),
        .RxUlpsEsc(InRxUlpsEsc),
        .RxTriggerEsc(InRxTriggerEsc),
        .EscBit(EscBit),
        .ErrControl(InErrControl),
        .ErrSyncEsc(InErrSyncEsc),
        .ErrEsc(InErrEsc),
        .LpFsmStop(LpFsmStop)
    );

    // Sequence Detector
    Sequence_Detector sequence_detector (
        .RxSymClkHS(RxSymClkHS),
        .RstN(RstN),
        .RxSymbol(RxSymbol),
        .HsSeqDetectorEn(HsSeqDetectorEn_sync),
        .DetectedSeq(DetectedSeq),
        .ErrSotSyncHs(InErrSotSyncHS),
        .ErrSotHS(InErrSotHS)
    );
    
    always@(posedge RxSymClkHS or negedge RstN)
    begin
        if(!RstN)
        begin
            DetectedSeq_REG <= 0;
            DetectedSeqREG  <= 0;
        end
        else
        begin
            DetectedSeq_REG <= DetectedSeq;
            DetectedSeqREG  <= DetectedSeq_REG;
        end
    end

    // Control Decoder
    Rx_Ctrl_Decoder rx_ctrl_decoder (
        .A(A),
        .B(B),
        .C(C),
        .CtrlDecoderEn(CtrlDecoderEn),
        .CtrlDecoderOut(CtrlDecoderOut)
    );
    

//======================================================================================================
//================================================= TX =================================================
//======================================================================================================    

    //Esc_Sequencer
    wire        EscSeqEn;
    wire        SeqBit;
    wire        CmdDone;
    wire [2:0]  EscSeqCtr;
    
    //ESC_Serializer
    wire        EscSerEn;
    wire        SerBit;
    wire        SerReadyEsc;
    wire        SerLastBit;
    
    //EscSerSeqMux
    wire        EscSerSeqEn;
    wire        EscBit_Encoder;
    
    //EscEncoder
    wire        EscEncoderEn;
    wire        EscEncoderDataValid;
    wire        EscEncoder_A;
    wire        EscEncoder_B;
    wire        EscEncoder_C;
    
    
    //Encoder
    wire        EncoderEn;
    //TX_Ctrl_Logic
    wire        TX_Ctrl_Logic_A;
    wire        TX_Ctrl_Logic_B;
    wire        TX_Ctrl_Logic_C;
    wire [1:0]  TxCtrlOut;
    
    //Mux_A-Mux_B-Mux_C
    wire        LpCtrEscSel;
    

//=======================================================================================================
// TX Path with Synchronizers
//=======================================================================================================
   synchronizer #(1) sync_EscSeqEn            (.clk(TxClkEsc),   .rst_n(RstN), .data_in(EscSeqEn),            .data_out(EscSeqEn_sync));
   synchronizer #(1) sync_EscSerEn            (.clk(TxClkEsc),   .rst_n(RstN), .data_in(EscSerEn),            .data_out(EscSerEn_sync));
   synchronizer #(1) sync_EscSerSeqEn         (.clk(TxClkEsc),   .rst_n(RstN), .data_in(EscSerSeqEn),         .data_out(EscSerSeqEn_sync));
   synchronizer #(1) sync_EscEncoderEn        (.clk(TxClkEsc),   .rst_n(RstN), .data_in(EscEncoderEn),        .data_out(EscEncoderEn_sync));
   synchronizer #(3) sync_EscSeqCtr           (.clk(TxClkEsc),   .rst_n(RstN), .data_in(EscSeqCtr),           .data_out(EscSeqCtr_sync));
   synchronizer #(2) sync_TxCtrlOut           (.clk(TxClkEsc),   .rst_n(RstN), .data_in(TxCtrlOut),           .data_out(TxCtrlOut_sync));
   synchronizer #(1) sync_EscEncoderDataValid (.clk(TxClkEsc),   .rst_n(RstN), .data_in(EscEncoderDataValid), .data_out(EscEncoderDataValid_sync));


        
    Esc_Sequencer Esc_Sequencer_U0 (
        .RstN           (RstN),
        .TxClkEsc       (TxClkEsc),
        .EscSeqEn       (EscSeqEn),
        .EscSeqCtr      (EscSeqCtr),
        .SeqBit         (SeqBit),
        .CmdDone        (CmdDone)
    );

    ESC_Serializer ESC_Serializerr_U0 (
        .TxClkEsc       (TxClkEsc),
        .RstN           (RstN),
        .TxDataEsc      (TxDataEsc),
        .EscSerEn       (EscSerEn),
        .TxReadyEsc     (SerReadyEsc),
        .LastBit        (SerLastBit),
        .SerBit         (SerBit)
    );

    Mux_1Bit      EscSerSeqMux (
        .A          (SeqBit),
        .B          (SerBit),
        .Sel        (EscSerSeqEn),
        .Out        (EscBit_Encoder)
    );

    Esc_Encoder    EscEncoder_U0 (
        .RST          (RstN),
        .TxClkEsc     (TxClkEsc),
        .EscBit       (EscBit_Encoder),
        .EscEncodeEn  (EscEncoderEn),
        .DataValid    (EscEncoderDataValid),
        .A            (EscEncoder_A),
        .B            (EscEncoder_B),
        .C            (EscEncoder_C)
    );


    TX_Ctrl_Logic    TX_Ctrl_Logic_U0 (
        .TxCtrlOut    (TxCtrlOut),
        .A            (TX_Ctrl_Logic_A),
        .B            (TX_Ctrl_Logic_B),
        .C            (TX_Ctrl_Logic_C)
    
    );
     
    Mux_1Bit        Mux_A_LP_TX (
        .A            (TX_Ctrl_Logic_A),
        .B            (EscEncoder_A),
        .Sel          (LpCtrEscSel),
        .Out          (LpTx[0])
    );
    
    Mux_1Bit        Mux_B_LP_TX (
        .A            (TX_Ctrl_Logic_B),
        .B            (EscEncoder_B),
        .Sel          (LpCtrEscSel),
        .Out          (LpTx[1])
    );
    
    Mux_1Bit        Mux_C_LP_TX (
        .A            (TX_Ctrl_Logic_C),
        .B            (EscEncoder_C),
        .Sel          (LpCtrEscSel),
        .Out          (LpTx[2])
    );
    
        
    ContentionDetection      contention_detection_U0 (
        .LpCdA      (LP_CD_A),
        .LpCdB      (LP_CD_B),
        .LpCdC      (LP_CD_C),
        .LpTxA      (LpTx[0]),
        .LpTxB      (LpTx[1]),
        .LpTxC      (LpTx[2]),
        .LpRxA      (A),
        .LpRxB      (B),
        .LpRxC      (C),
        .ErrContentionP0      (ErrContentionLP0),
        .ErrContentionP1      (ErrContentionLP1)   
    );
//=======================================================================================================
// FSM Input Synchronization
//=======================================================================================================
    // NEW SYNC: RX Domain to FSM Sync
	synchronizer #(4) sync_DetectedSeq    
    (.clk(RxClkFsm), .rst_n(RstN), .data_in(DetectedSeqREG),        .data_out(DetectedSeq_sync));
    synchronizer #(2) sync_CtrlDecoderOut 
    (.clk(RxClkFsm), .rst_n(RstN), .data_in(CtrlDecoderOut),     .data_out(CtrlDecoderOut_sync));
    synchronizer #(1) sync_LpFsmStop      
    (.clk(RxClkFsm), .rst_n(RstN), .data_in(LpFsmStop),          .data_out(LpFsmStop_sync));
    synchronizer #(1) sync_InRxValidEsc   
    (.clk(RxClkFsm), .rst_n(RstN), .data_in(InRxValidEsc),       .data_out(InRxValidEsc_sync));
    synchronizer #(4) sync_InRxTriggerEsc 
    (.clk(RxClkFsm), .rst_n(RstN), .data_in(InRxTriggerEsc),     .data_out(InRxTriggerEsc_sync));
    synchronizer #(1) sync_InRxUlpsEsc    
    (.clk(RxClkFsm), .rst_n(RstN), .data_in(InRxUlpsEsc),        .data_out(InRxUlpsEsc_sync));
    synchronizer #(1) sync_InRxLpdtEsc    
    (.clk(RxClkFsm), .rst_n(RstN), .data_in(InRxLpdtEsc),        .data_out(InRxLpdtEsc_sync));
    synchronizer #(1) sync_InRxInvalidCodeHS      
    (.clk(RxClkFsm), .rst_n(RstN), .data_in(InRxInvalidCodeHS),  .data_out(InRxInvalidCodeHS_sync));
    synchronizer #(1) sync_InErrSotHS     
    (.clk(RxClkFsm), .rst_n(RstN), .data_in(InErrSotHS),         .data_out(InErrSotHS_sync));
    synchronizer #(1) sync_InErrSotSyncHS      
    (.clk(RxClkFsm), .rst_n(RstN), .data_in(InErrSotSyncHS),     .data_out(InErrSotSyncHS_sync));
    synchronizer #(1) sync_InErrEsc       
    (.clk(RxClkFsm), .rst_n(RstN), .data_in(InErrEsc),           .data_out(InErrEsc_sync));
    synchronizer #(1) sync_InErrSyncEsc   
    (.clk(RxClkFsm), .rst_n(RstN), .data_in(InErrSyncEsc),       .data_out(InErrSyncEsc_sync));
    synchronizer #(1) sync_InErrControl   
    (.clk(RxClkFsm), .rst_n(RstN), .data_in(InErrControl),       .data_out(InErrControl_sync));
    // NEW SYNC: TX Domain to FSM Sync
    synchronizer #(1) sync_TxReqEsc     
	(.clk(RxClkFsm), .rst_n(RstN), .data_in(TxReqEsc),          .data_out(TxReqEsc_sync));
    synchronizer #(1) sync_TxValidEsc                           
	(.clk(RxClkFsm), .rst_n(RstN), .data_in(TxValidEsc),        .data_out(TxValidEsc_sync));
    synchronizer #(1) sync_TxUlpsEsc                            
	(.clk(RxClkFsm), .rst_n(RstN), .data_in(TxUlpsEsc),         .data_out(TxUlpsEsc_sync  ));
    synchronizer #(1) sync_TxLpdtEsc                            
	(.clk(RxClkFsm), .rst_n(RstN), .data_in(TxLpdtEsc),         .data_out(TxLpdtEsc_sync  ));
    synchronizer #(1) sync_TxUlpsExit                           
	(.clk(RxClkFsm), .rst_n(RstN), .data_in(TxUlpsExit),        .data_out(TxUlpsExit_sync ));
    synchronizer #(1) sync_CmdDone                              
	(.clk(RxClkFsm), .rst_n(RstN), .data_in(CmdDone),           .data_out(CmdDone_sync    ));
    synchronizer #(1) sync_SerReadyEsc                          
	(.clk(RxClkFsm), .rst_n(RstN), .data_in(SerReadyEsc),       .data_out(SerReadyEsc_sync));
    synchronizer #(1) sync_SerLastBit                           
	(.clk(RxClkFsm), .rst_n(RstN), .data_in(SerLastBit),        .data_out(SerLastBit_sync ));
    synchronizer #(4) sync_TxTriggerEsc                         
	(.clk(RxClkFsm), .rst_n(RstN), .data_in(TxTriggerEsc),      .data_out(TxTriggerEsc_sync));     

//======================================================================================================
//=========================================== Full FSM =================================================
//======================================================================================================

    // Instantiate SlaveFSM
    SlaveFSM slave_fsm_inst (
		// Clock and Reset
        .RxClkFsm(RxClkFsm),
        .RstN(RstN),
		// Control Signals
		.TurnDisable(TurnDisable),                           
        .ForceRxmode(ForceRxmode),
        .TurnRequest(TurnRequest),        
        .ForceTxStopmode(ForceTxStopmode),    
        .Enable(Enable),    
		// RX Signals (LP & HS)
		// Inputs 	
        .LpCLK(RxClkEscOut),                                
        .LpFsmStop     (LpFsmStop_sync),
        .CtrlDecoderOut(CtrlDecoderOut_sync), 
        .InRxValidEsc  (InRxValidEsc_sync),                                           
        .InRxTriggerEsc(InRxTriggerEsc_sync),
        .InRxUlpsEsc   (InRxUlpsEsc_sync),
        .InRxLpdtEsc   (InRxLpdtEsc_sync),
        .InErrEsc      (InErrEsc_sync),
        .InErrSyncEsc  (InErrSyncEsc_sync),
        .InErrControl  (InErrControl_sync),
        .HsCLK(RxWordClkHS),                           ////////////////////// change from sym to word clk
        .DetectedSeq   (DetectedSeq_sync),
        .InRxInvalidCodeHS(InRxInvalidCodeHS_sync),
        .InErrSotHS    (InErrSotHS_sync),
        .InErrSotSyncHS(InErrSotSyncHS_sync),
        // Outputs
        .HsRxEn(HsRxEn),
        .HsSettleExp(HsSettleExp),
        .HsDecoderEn(HsDecoderEn),
        .HSDeserEn(HSDeserEn),
        .HsSeqDetectorEn(HsSeqDetectorEn),
        .RxWordClkHS(RxWordClkHS_out),             ///////// add out port with name RxWordClkHS_out
        .RxInvalidCodeHS(RxInvalidCodeHS),
        .RxValidHS(RxValidHS),                                          
        .RxActiveHS(RxActiveHS),
        .RxSyncHS(RxSyncHS),
        .ErrSotHS(ErrSotHS),
        .ErrSotSyncHS(ErrSotSyncHS),
        .LpRxEn(LpRxEn),                                                  
        .EscDecoderEn(EscDecoderEn),
        .EscDeserEn(EscDeserEn),
        .RxClkEsc(RxClkEsc),                
        .RxValidEsc(RxValidEsc),
        .RxTriggerEsc(RxTriggerEsc),
        .RxUlpsEsc(RxUlpsEsc),
        .RxLpdtEsc(RxLpdtEsc),
        .ErrEsc(ErrEsc),
        .ErrSyncEsc(ErrSyncEsc),
        .ErrControl(ErrControl),
        .CtrlDecoderEn(CtrlDecoderEn),
		.RequestDetection(RequestDetection),
        // TX Signals (LP)
		// Inputs 	
		.TxReqEsc     (TxReqEsc_sync),
		.TxValidEsc   (TxValidEsc_sync),
		.TxUlpdtEsc   (TxUlpsEsc_sync),
		.TxLpdtEsc    (TxLpdtEsc_sync),
		.TxUlpdtExit  (TxUlpsExit_sync),
		.TxTriggerEsc (TxTriggerEsc_sync),
		.CmdDone      (CmdDone_sync),
		.SerReadyEsc  (SerReadyEsc_sync),
		.SerLastBit   (SerLastBit_sync),
		// Outputs
		.TxReadyEsc    (TxReadyEsc),             
		.EscSeqEn      (EscSeqEn),
		.EscSerEn      (EscSerEn),
		.EscSerSeqSel  (EscSerSeqEn),
		.EscEncoderEn  (EscEncoderEn),
		.LpCtrlEscSel  (LpCtrEscSel),
		.EscSeqCtr     (EscSeqCtr),
		.TxCtrlOut     (TxCtrlOut),
		.LpTxEn        (LpTxEn),
		.EscEncoderDataValid(EscEncoderDataValid),
		// Interface Signals
        .Direction(Direction),
        .Stopstate(Stopstate),
        .UlpsActiveNot(UlpsActiveNot)
    );

endmodule