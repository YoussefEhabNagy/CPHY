//=================================================================================================
//  File Name    : Master_tb.sv
//  Description  : 
//      This SystemVerilog testbench verifies the functionality of the full C-PHY master module,
//      particularly the behavior of both the RX and TX FSMs in HS (High-Speed), LP (Low-Power),
//      and Escape modes. It coordinates stimulus generation, monitors transitions, and checks
//      for protocol compliance and correct signal behavior.
//
//      The testbench includes:
//      - Global reset and signal initialization
//      - TX path validation: Preamble, Sync Word, Data, and Post-amble sequences
//      - TX & RX path testing: Escape Mode entry, Commands, LPDT, ULPS
//      - Turnaround validation: RX-to-TX and TX-to-RX with proper timing
//      - Forced mode activation and error checking
//
//  Key Inputs    :
//      - RstN                    : Active-low asynchronous reset
//      - TxDataHS[15:0]          : Input high-speed data bus
//      - TxSendSyncHS            : Triggers sync word transmission
//      - TxReqHS                 : Requests HS transmission start
//      - TxReqEsc, TxLpdtEsc     : Escape Mode entry and LPDT trigger
//      - TxUlpsEsc, TxUlpsExit   : ULPS entry and exit control
//      - TxTriggerEsc[3:0]       : Escape trigger value
//      - TxDataEsc[7:0]          : Escape mode data input
//      - TxValidEsc              : Escape data valid indicator
//      - LpRx[2:0]               : Low-power RX input bus (control + data)
//      - TurnRequest             : Requests TX ↔ RX turnaround
//      - TurnDisable             : Disables RX-to-TX turnaround
//      - ForceRxmode             : Forces RX mode override
//      - ForceTxStopmode         : Forces TX stop state entry
//      - Enable                  : Master enable signal
//      - LP_CD_A/B/C             : Contention detection inputs (should match LpTx values)
//
//  Key Outputs   :
//      - TxReadyHS               : Indicates HS data word accepted
//      - A, B, C[1:0]            : HS encoded symbol outputs
//      - HsTxEn                  : Tristate buffer enable for HS output
//      - TxReadyEsc              : Indicates Escape data word accepted
//      - LpTx[2:0]               : LP output signals
//      - LpTxEn                  : Tristate buffer enable for LP mode
//      - RxClkEscOut             : Recovered Escape clock from RX
//      - RxLpdtEsc               : Escape LPDT RX indicator
//      - RxUlpsEsc               : Escape ULPS RX indicator
//      - RxTriggerEsc[3:0]       : Escape trigger value received
//      - RxEscData[7:0]          : Escape data
//      - RxValidEsc              : Escape data valid flag
//      - Direction               : 1=RX mode, 0=TX mode
//      - Stopstate               : High when in idle stop state
//      - UlpsActiveNot           : Exit from ULPS state flag 0= asserted
//      - ErrEsc                  : Invalid escape command error
//      - ErrSyncEsc              : Escape data misalignment error
//      - ErrControl              : Control FSM sequence error
//      - ErrContentionLP0/LP1    : Contention errors while driving 0/1
//      - ErrSotHS                : Start-of-transmission HS error
//      - ErrSotSyncHS            : Sync word mismatch in HS mode
//
//  Tasks & Test Sequences:
//      - Initialize()                    : Initializes DUT and signals
//      - Reset_Enable()                  : Applies reset and sets initial configuration
//      - Stop_Check() / Rx_Stop_Check()  : Validates Stop state after TX/RX transitions
//      - Basic_HS_transmission()         : Tests single HS word encoding
//      - HS_continuous_data()            : Streams multiple HS words
//      - HS_word_sync_transmission()     : Sends sync word before HS data
//      - Valid_LPDT_data_transmission()  : Sends valid LPDT escape data
//      - Multiple_LPDT_bytes()           : Streams multiple LPDT words
//      - No_TxValidEsc_asserted()        : Tests handling when TxValidEsc not asserted
//      - Enter_ULPS_mode()               : Enters Ultra Low Power State
//      - Exit_ULPS_mode()                : Exits ULPS and checks recovery
//      - TX_to_RX_Turnaround()           : Tests turnaround with TurnRequest
//      - TX_to_RX_with_TurnDisable()     : Ensures TurnDisable prevents transition
//      - Force_TxStopmode()              : Forces TX stop state
//      - Force_RxMode()                  : Overrides FSM to RX mode
//
//  Clock Domains:
//      - TxSymbolClkHS (2.1 GHz)   : Drives HS symbol serialization
//      - TxWordClkHS   (300 MHz)   : Feeds word data to the TX FSM, FSM operation
//      - TxClkEsc      (10 MHz)    : Operates Escape mode
//
//  Assertions:
//      - FSM State Assertions:
//          - TX FSM states: TX_HS_REQUEST_P, TX_LP_RQST_P, TX_HS_PREPARE_P, TX_LP_YIELD_P,
//                           TX_HS_PREAMBLE_P, TX_HS_SYNC_WORD_P, TX_HS_SEND_DATA_P, TX_HS_POST_P,
//                           TX_TA_REQUEST_P, TX_TA_GO_P, TX_ESC_RQST_P, TX_ESC_GO_P, TX_ESC_CMD_P,
//                           TX_LPDT_P, TX_LPDT_Pause_P, TX_TRIGGERS_P, TX_ULPS_P
//          - RX FSM states: RX_TA_LOOK_P, RX_TA_ACK_P
//          - Mode Forcing:   FORCE_RX_P
//      - Post Check Assertion:
//          - Post_Check: Validates correctness of Post state signal behavior based on prior output line inversions (A, B, C)
//
//  Authors      : Youssef Ehab (TX FSM <HS, LP>), Mohamed Emam (RX FSM <LP>)
//  Date         : 26/5/2025
//=================================================================================================


`timescale 1ns / 1ps

module Master_tb;

  // Timer parameters in clock cycles 
  parameter LP_TX_TIME     = 50  ;   
  parameter TERMEN_TIME    = 50  ;   
  parameter SETTLE_TIME    = 100 ;  
  parameter TA_SURE_TIME   = 100 ;  
  parameter TA_GET_TIME    = 250 ;  
  parameter WAKE_UP_TIME   = 1000;

  /////////////////////////
  ///////  Inputs  //////// 
  /////////////////////////

  reg RstN;
  reg TxSymbolClkHS;
  reg TxWordClkHs;

  reg [15:0] TxDataHS;
  reg TxSendSyncHS;
  reg TxReqHS;

  reg TxClkEsc;
  reg TxReqEsc;
  reg TxLpdtEsc;
  reg TxUlpsEsc;
  reg TxUlpsExit;
  reg [3:0] TxTriggerEsc;
  reg [7:0] TxDataEsc;
  reg TxValidEsc;

  reg [2:0] LpRx;

  reg TurnRequest;
  reg TurnDisable;
  reg ForceRxmode;
  reg ForceTxStopmode;
  reg Enable;

  reg LP_CD_A;
  reg LP_CD_B;
  reg LP_CD_C;

  /////////////////////////
  ///////  Outputs  /////// 
  /////////////////////////

  wire TxReadyHS;
  wire [7:0] A, B, C;
  wire TxReadyEsc;
  wire LpRxEn;
  wire RxClkEscOut;
  wire RxLpdtEsc;
  wire RxUlpsEsc;
  wire [3:0] RxTriggerEsc;
  wire [7:0] RxEscData;
  wire Direction;
  wire Stopstate;
  wire UlpsActiveNot;
  wire RxValidEsc;
  wire ErrEsc;
  wire ErrSyncEsc;
  wire ErrControl;
  wire ErrContentionLP0;
  wire ErrContentionLP1;
  wire ErrSotHS;
  wire ErrSotSyncHS;

  //====================================================================
  //==================== Design Instaniation ===========================
  //====================================================================

  Master DUT (
  .RstN(RstN), .TxSymbolClkHS(TxSymbolClkHS), .TxWordClkHs(TxWordClkHs),
  .TxDataHS(TxDataHS), .TxSendSyncHS(TxSendSyncHS), .TxReqHS(TxReqHS),
  .TxClkEsc(TxClkEsc), .TxReqEsc(TxReqEsc), .TxLpdtEsc(TxLpdtEsc),
  .TxUlpsEsc(TxUlpsEsc), .TxUlpsExit(TxUlpsExit), .TxTriggerEsc(TxTriggerEsc),
  .TxDataEsc(TxDataEsc), .TxValidEsc(TxValidEsc), .LpRx(LpRx),
  .TurnRequest(TurnRequest), .TurnDisable(TurnDisable), .ForceRxmode(ForceRxmode),
  .ForceTxStopmode(ForceTxStopmode), .Enable(Enable), .LP_CD_A(LP_CD_A),
  .LP_CD_B(LP_CD_B), .LP_CD_C(LP_CD_C),
  .TxReadyHS(TxReadyHS), .A(A), .B(B), .C(C),
  .TxReadyEsc(TxReadyEsc), .RxClkEsc(RxClkEscOut),
  .RxLpdtEsc(RxLpdtEsc), .RxUlpsEsc(RxUlpsEsc), .RxTriggerEsc(RxTriggerEsc),
  .RxEscData(RxEscData), .RxValidEsc(RxValidEsc),
  .Direction(Direction), .LpRxEn(LpRxEn),
  .Stopstate(Stopstate), .UlpsActiveNot(UlpsActiveNot), .ErrEsc(ErrEsc),
  .ErrSyncEsc(ErrSyncEsc), .ErrControl(ErrControl), .ErrContentionLP0(ErrContentionLP0),
  .ErrContentionLP1(ErrContentionLP1),
  .ErrSotHS(ErrSotHS),
  .ErrSotSyncHS(ErrSotSyncHS)
  );


  //====================================================================
  //======================= Clock generation ===========================
  //====================================================================
    
  initial begin
    TxWordClkHs = 0;
    forever #1.68 TxWordClkHs = ~TxWordClkHs;
  end

  initial begin
    TxSymbolClkHS = 0;
    forever #0.24 TxSymbolClkHS = ~TxSymbolClkHS;
  end

  initial begin
    TxClkEsc = 0;
    forever #50 TxClkEsc = ~TxClkEsc;
  end

  //====================================================================
  //========================== Initial block ===========================
  //====================================================================

  initial begin
    // Initialization
    Initialize();
    // Reset and enable
    Reset_Enable();

    //Check stop state
    Stop_Check();

    //====================================================//
    //=================== TX Test Cases ==================//
    //====================================================//


    $display("\n\n//=================== TX Test Cases ==================//\n\n");
    // === TC_HS_01: Basic HS transmission ===
    
    Basic_HS_transmission();
    Stop_Check();

    // === TC_HS_02: HS continuous data ===
    HS_continuous_data();
    Stop_Check();

    // === TC_HS_03: HS word sync transmission ===
    
    HS_word_sync_transmission();
    Stop_Check();

    // === TC_ESC_01: Valid LPDT data transmission ===
    
    Valid_LPDT_data_transmission();
    Stop_Check();

    // === TC_ESC_02: Multiple LPDT bytes ===
    
    Multiple_LPDT_bytes();
    Stop_Check();

    // === TC_ESC_03: No TxValidEsc asserted ===
    No_TxValidEsc_asserted();
    Stop_Check();

    // === TC_ESC_04: Enter ULPS mode ===
    
    Enter_ULPS_mode();
    Ulps_Check();

    // === TC_ESC_05: Exit ULPS mode ===
    
    Exit_ULPS_mode();
    Stop_Check();

    // === TC_ESC_06: Reset Trigger ===
    
    Reset_Trigger();
    Stop_Check();

    // === TC_TURN_01: TX to RX Turnaround ===
    
    TX_to_RX_Turnaround();
    Rx_Stop_Check();

    // === TC_FORCE_01: Force TxStopmode ===
    
    Force_TxStopmode();
    Stop_Check();

    // === TC_TURN_02: TX to RX with TurnDisable ===
    
    TX_to_RX_with_TurnDisable();
    Stop_Check();

    // === TC_FORCE_02: Force RxMode ===
    
    Force_RxMode();
    Rx_Stop_Check();

    
    //====================================================//
    //=================== RX Test Cases ==================//
    //====================================================//
    

    $display("\n\n//=================== RX Test Cases ==================//\n\n");
    
    //=================== LP ESC Senario =======================
    //Receving LpRequest
    LpRequest(); // From RX_STOP to RX_LP_RQST to RX_LP_YIELD 
    assert_Lp_state(DUT.cphy_tx_fsm_U0.RX_LP_YIELD,"RX_LP_YIELD");
    //Receving EscapeEntry
    EscapeEntry(); // From RX_LP_YIELD to RX_ESC_RQST to RX_Esc_Go
    assert_Lp_state(DUT.cphy_tx_fsm_U0.RX_Esc_Go,"RX_Esc_Go");
    //Receving Command
    CommandSend();
    //Receving LpData
    LpData();
    assert_Lp_state(DUT.cphy_tx_fsm_U0.RX_LPDT,"RX_LPDT");
    //Receving Spacs
    space();
    assert_Lp_state(DUT.cphy_tx_fsm_U0.RX_LPDT,"RX_LPDT");
    //Receving LpData
    LpData();
    assert_Lp_state(DUT.cphy_tx_fsm_U0.RX_LPDT,"RX_LPDT");
    //Receving EndEscape
    EndEscape();
    assert_Lp_state(DUT.cphy_tx_fsm_U0.RX_STOP,"RX_STOP");
    
    //=================== Turnaround Senario ==================
    //Receving LpRequest
    LpRequest(); // From RX_STOP to RX_LP_RQST to RX_LP_YIELD 
    assert_Lp_state(DUT.cphy_tx_fsm_U0.RX_LP_YIELD,"RX_LP_YIELD");
    //Receving Turnaround
    Turnaround(); // From RX_LP_YIELD to RX_TA_RQST to RX_TA_WAIT
    assert_Lp_state(DUT.cphy_tx_fsm_U0.RX_TA_WAIT,"RX_TA_WAIT");
    // Waiting for tTA-SURE
    #(TA_SURE_TIME) // From RX_TA_WAIT to TX_TA_GET
    assert_Lp_state(DUT.cphy_tx_fsm_U0.TX_TA_GET,"TX_TA_GET");
    // Waiting for tTA-GET
    #(TA_GET_TIME) // From TX_TA_GET to TX_TA_ACK
    assert_Lp_state(DUT.cphy_tx_fsm_U0.TX_TA_ACK,"TX_TA_ACK");
    // Waiting for tLPX
    #(LP_TX_TIME) // From TX_TA_ACK to TX_STOP
    #20; //Time due to sync latency
    assert_Lp_state(DUT.cphy_tx_fsm_U0.TX_STOP,"TX_STOP");

    $display("All test cases completed.");
    $stop;
  end

  //====================================================================
  //========================== Assertions ==============================
  //====================================================================

  //////////////// Ready Check //////////////////////
    reg WaitHs;
    reg WaitEsc;
    reg WaitNotEsc;

    property ReadyHs_Wait_Time_Out;
    @(posedge TxWordClkHs)
      disable iff (!RstN)
      WaitHs |=> ##[0:52] TxReadyHS; //48 cycles => 16 preamble + 32 Transition from stop state till HS Setup
    endproperty

    property ReadyEsc_Wait_Time_Out;
    @(posedge TxWordClkHs)
      disable iff (!RstN)
      WaitEsc |=> ##[0:441] TxReadyEsc; //439 cycles => (8-bit Esc clock) Command + reaching command state + synchronizers latency
    endproperty

    property Not_ReadyEsc_Wait_Time_Out;
    @(posedge TxWordClkHs)
      disable iff (!RstN)
      WaitNotEsc |=> ##[0:600] !TxReadyEsc;
    endproperty


    string Ready_Num;

    assert property (ReadyHs_Wait_Time_Out)
    else $fatal("ERROR: 'HS ready %s' was not asserted within 48 cycles!",Ready_Num);
    assert property (ReadyEsc_Wait_Time_Out)
    else $fatal("ERROR: 'Esc ready %s' was not asserted within 313 cycles!",Ready_Num);
    assert property (Not_ReadyEsc_Wait_Time_Out)
    else $fatal("ERROR: 'Esc ready %s' was not deasserted",Ready_Num);

  /////////////// States Outputs check //////////////

  // State definitions 
localparam [5:0] 
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
    FORCE_RX            = 6'd28,
    TX_ESC_GO           = 6'd29, 
    TX_ESC_CMD          = 6'd30, 
    TX_LPDT             = 6'd31,  
    TX_TRIGGERS         = 6'd32,  
    TX_ULPS             = 6'd33,  
    TX_LPDT_Pause       = 6'd35;

  task print_signals;
  $display("--------------------------------------------------");
  $display("Printing FSM internal signal values:");
  $display("State: %0d", DUT.cphy_tx_fsm_U0.current_state);
  $display("HsSerializerEn       = %0d", DUT.cphy_tx_fsm_U0.HsSerializerEn);
  $display("SerSeqSel            = %0d", DUT.cphy_tx_fsm_U0.SerSeqSel);
  $display("EncoderEn            = %0d", DUT.cphy_tx_fsm_U0.EncoderEn);
  $display("TxReadyHS            = %0d", DUT.cphy_tx_fsm_U0.TxReadyHS);
  $display("TxReadyEsc           = %0d", DUT.cphy_tx_fsm_U0.TxReadyEsc);
  $display("Direction            = %0d", DUT.cphy_tx_fsm_U0.Direction);
  $display("Stopstate            = %0d", DUT.cphy_tx_fsm_U0.Stopstate);
  $display("EscSerEn             = %0d", DUT.cphy_tx_fsm_U0.EscSerEn);
  $display("EscSerSeqSel         = %0d", DUT.cphy_tx_fsm_U0.EscSerSeqSel);
  $display("EscEncoderEn         = %0d", DUT.cphy_tx_fsm_U0.EscEncoderEn);
  $display("TxCtrlOut            = %b",  DUT.cphy_tx_fsm_U0.TxCtrlOut);
  $display("LpCtrlEscSel         = %0d", DUT.cphy_tx_fsm_U0.LpCtrlEscSel);
  $display("LpTxEn               = %0d", DUT.cphy_tx_fsm_U0.LpTxEn);
  $display("HsTxEn               = %0d", DUT.cphy_tx_fsm_U0.HsTxEn);
  $display("LpRxEn               = %0d", DUT.cphy_tx_fsm_U0.LpRxEn);
  $display("Timer_En             = %0d", DUT.cphy_tx_fsm_U0.Timer_En);
  $display("Timer_Seed           = %0d", DUT.cphy_tx_fsm_U0.Timer_Seed);
  $display("HsSeqCtr             = %0d", DUT.cphy_tx_fsm_U0.HsSeqCtr);
  $display("EscSeqCtr            = %0d", DUT.cphy_tx_fsm_U0.EscSeqCtr);
  $display("--------------------------------------------------");
  endtask


  property TX_HS_REQUEST_P;
    @(posedge TxWordClkHs)
      disable iff (!RstN)
      (DUT.cphy_tx_fsm_U0.current_state == TX_HS_REQUEST) |-> (
        (DUT.cphy_tx_fsm_U0.HsSerializerEn == 0) &&
        (DUT.cphy_tx_fsm_U0.SerSeqSel == 0) &&
        (DUT.cphy_tx_fsm_U0.EncoderEn == 0) &&
        (DUT.cphy_tx_fsm_U0.TxReadyHS == 0) &&
        (DUT.cphy_tx_fsm_U0.TxReadyEsc == 0) &&
        (DUT.cphy_tx_fsm_U0.Direction == 0) &&
        (DUT.cphy_tx_fsm_U0.Stopstate == 0) &&
        (DUT.cphy_tx_fsm_U0.EscSerEn == 0) &&
        (DUT.cphy_tx_fsm_U0.EscSerSeqSel == 0) &&
        (DUT.cphy_tx_fsm_U0.EscEncoderEn == 0) &&
        (DUT.cphy_tx_fsm_U0.TxCtrlOut == 2'b01) &&
        (DUT.cphy_tx_fsm_U0.LpCtrlEscSel == 0) &&
        (DUT.cphy_tx_fsm_U0.LpTxEn == 1) &&
        (DUT.cphy_tx_fsm_U0.HsTxEn == 0) &&
        (DUT.cphy_tx_fsm_U0.LpRxEn == 0) &&
        (DUT.cphy_tx_fsm_U0.Timer_En == 1) &&
        (DUT.cphy_tx_fsm_U0.Timer_Seed == 0) &&
        (DUT.cphy_tx_fsm_U0.HsSeqCtr == 0)
        ); 
  endproperty
  property TX_LP_RQST_P;
    @(posedge TxWordClkHs)
      disable iff (!RstN)
      (DUT.cphy_tx_fsm_U0.current_state == TX_LP_RQST) |-> (
        (DUT.cphy_tx_fsm_U0.HsSerializerEn == 0) &&
        (DUT.cphy_tx_fsm_U0.SerSeqSel == 0) &&
        (DUT.cphy_tx_fsm_U0.EncoderEn == 0) &&
        (DUT.cphy_tx_fsm_U0.TxReadyHS == 0) &&
        (DUT.cphy_tx_fsm_U0.TxReadyEsc == 0) &&
        (DUT.cphy_tx_fsm_U0.Direction == 0) &&
        (DUT.cphy_tx_fsm_U0.Stopstate == 0) &&
        (DUT.cphy_tx_fsm_U0.EscSerEn == 0) &&
        (DUT.cphy_tx_fsm_U0.EscSerSeqSel == 0) &&
        (DUT.cphy_tx_fsm_U0.EscEncoderEn == 0) &&
        (DUT.cphy_tx_fsm_U0.TxCtrlOut == 2'b11) &&
        (DUT.cphy_tx_fsm_U0.LpCtrlEscSel == 0) &&
        (DUT.cphy_tx_fsm_U0.LpTxEn == 1) &&
        (DUT.cphy_tx_fsm_U0.HsTxEn == 0) &&
        (DUT.cphy_tx_fsm_U0.LpRxEn == 1) &&
        (DUT.cphy_tx_fsm_U0.Timer_En == 1) &&
        (DUT.cphy_tx_fsm_U0.Timer_Seed == 0) &&
        (DUT.cphy_tx_fsm_U0.HsSeqCtr == 0)
        ); 
  endproperty
  property TX_HS_PREPARE_P;
    @(posedge TxWordClkHs)
      disable iff (!RstN)
      (DUT.cphy_tx_fsm_U0.current_state == TX_HS_PREPARE) |-> (
        (DUT.cphy_tx_fsm_U0.HsSerializerEn == 0) &&
        (DUT.cphy_tx_fsm_U0.SerSeqSel == 0) &&
        (DUT.cphy_tx_fsm_U0.EncoderEn == 0) &&
        (DUT.cphy_tx_fsm_U0.TxReadyHS == 0) &&
        (DUT.cphy_tx_fsm_U0.TxReadyEsc == 0) &&
        (DUT.cphy_tx_fsm_U0.Direction == 0) &&
        (DUT.cphy_tx_fsm_U0.Stopstate == 0) &&
        (DUT.cphy_tx_fsm_U0.EscSerEn == 0) &&
        (DUT.cphy_tx_fsm_U0.EscSerSeqSel == 0) &&
        (DUT.cphy_tx_fsm_U0.EscEncoderEn == 0) &&
        (DUT.cphy_tx_fsm_U0.TxCtrlOut == 2'b10) &&
        (DUT.cphy_tx_fsm_U0.LpCtrlEscSel == 0) &&
        (DUT.cphy_tx_fsm_U0.LpTxEn == 1) &&
        (DUT.cphy_tx_fsm_U0.HsTxEn == 0) &&
        (DUT.cphy_tx_fsm_U0.LpRxEn == 0) &&
        (DUT.cphy_tx_fsm_U0.Timer_En == 1) &&
        (DUT.cphy_tx_fsm_U0.Timer_Seed == 0) &&
        (DUT.cphy_tx_fsm_U0.HsSeqCtr == 0)
        ); 
  endproperty
  property TX_LP_YIELD_P;
    @(posedge TxWordClkHs)
      disable iff (!RstN)
      (DUT.cphy_tx_fsm_U0.current_state == TX_LP_YIELD) |-> (
        (DUT.cphy_tx_fsm_U0.HsSerializerEn == 0) &&
        (DUT.cphy_tx_fsm_U0.SerSeqSel == 0) &&
        (DUT.cphy_tx_fsm_U0.EncoderEn == 0) &&
        (DUT.cphy_tx_fsm_U0.TxReadyHS == 0) &&
        (DUT.cphy_tx_fsm_U0.TxReadyEsc == 0) &&
        (DUT.cphy_tx_fsm_U0.Direction == 0) &&
        (DUT.cphy_tx_fsm_U0.Stopstate == 0) &&
        (DUT.cphy_tx_fsm_U0.EscSerEn == 0) &&
        (DUT.cphy_tx_fsm_U0.EscSerSeqSel == 0) &&
        (DUT.cphy_tx_fsm_U0.EscEncoderEn == 0) &&
        (DUT.cphy_tx_fsm_U0.TxCtrlOut == 2'b10) &&
        (DUT.cphy_tx_fsm_U0.LpCtrlEscSel == 0) &&
        (DUT.cphy_tx_fsm_U0.LpTxEn == 1) &&
        (DUT.cphy_tx_fsm_U0.HsTxEn == 0) &&
        (DUT.cphy_tx_fsm_U0.LpRxEn == 1) &&
        (DUT.cphy_tx_fsm_U0.Timer_En == 1) &&
        (DUT.cphy_tx_fsm_U0.Timer_Seed == 0) &&
        (DUT.cphy_tx_fsm_U0.HsSeqCtr == 0)
        ); 
  endproperty
  property TX_HS_PREAMBLE_P;
    @(posedge TxWordClkHs)
      disable iff (!RstN)
      (DUT.cphy_tx_fsm_U0.current_state == TX_HS_PREAMBLE) |-> (
        (DUT.cphy_tx_fsm_U0.HsSerializerEn == 0) &&
        (DUT.cphy_tx_fsm_U0.SerSeqSel == 0) &&
        (DUT.cphy_tx_fsm_U0.EncoderEn == 1) &&
        (DUT.cphy_tx_fsm_U0.TxReadyHS == 0) &&
        (DUT.cphy_tx_fsm_U0.TxReadyEsc == 0) &&
        (DUT.cphy_tx_fsm_U0.Direction == 0) &&
        (DUT.cphy_tx_fsm_U0.Stopstate == 0) &&
        (DUT.cphy_tx_fsm_U0.EscSerEn == 0) &&
        (DUT.cphy_tx_fsm_U0.EscSerSeqSel == 0) &&
        (DUT.cphy_tx_fsm_U0.EscEncoderEn == 0) &&
        (DUT.cphy_tx_fsm_U0.TxCtrlOut == 2'b10) &&
        (DUT.cphy_tx_fsm_U0.LpCtrlEscSel == 0) &&
        (DUT.cphy_tx_fsm_U0.LpTxEn == 0) &&
        (DUT.cphy_tx_fsm_U0.HsTxEn == 1) &&
        (DUT.cphy_tx_fsm_U0.LpRxEn == 0) &&
        (DUT.cphy_tx_fsm_U0.Timer_En == 0) &&
        (DUT.cphy_tx_fsm_U0.Timer_Seed == 0) &&
        (DUT.cphy_tx_fsm_U0.HsSeqCtr == 4)
        ); 
  endproperty
  property TX_TA_REQUEST_P;
    @(posedge TxWordClkHs)
      disable iff (!RstN)
      (DUT.cphy_tx_fsm_U0.current_state == TX_TA_REQUEST) |-> (
        (DUT.cphy_tx_fsm_U0.HsSerializerEn == 0) &&
        (DUT.cphy_tx_fsm_U0.SerSeqSel == 0) &&
        (DUT.cphy_tx_fsm_U0.EncoderEn == 0) &&
        (DUT.cphy_tx_fsm_U0.TxReadyHS == 0) &&
        (DUT.cphy_tx_fsm_U0.TxReadyEsc == 0) &&
        (DUT.cphy_tx_fsm_U0.Direction == 0) &&
        (DUT.cphy_tx_fsm_U0.Stopstate == 0) &&
        (DUT.cphy_tx_fsm_U0.EscSerEn == 0) &&
        (DUT.cphy_tx_fsm_U0.EscSerSeqSel == 0) &&
        (DUT.cphy_tx_fsm_U0.EscEncoderEn == 0) &&
        (DUT.cphy_tx_fsm_U0.TxCtrlOut == 2'b11) &&
        (DUT.cphy_tx_fsm_U0.LpCtrlEscSel == 0) &&
        (DUT.cphy_tx_fsm_U0.LpTxEn == 1) &&
        (DUT.cphy_tx_fsm_U0.HsTxEn == 0) &&
        (DUT.cphy_tx_fsm_U0.LpRxEn == 1) &&
        (DUT.cphy_tx_fsm_U0.Timer_En == 1) &&
        (DUT.cphy_tx_fsm_U0.Timer_Seed == 0) &&
        (DUT.cphy_tx_fsm_U0.HsSeqCtr == 0)
        ); 
  endproperty
  property TX_ESC_RQST_P;
    @(posedge TxWordClkHs)
      disable iff (!RstN)
      (DUT.cphy_tx_fsm_U0.current_state == TX_ESC_RQST) |-> (
        (DUT.cphy_tx_fsm_U0.HsSerializerEn == 0) &&
        (DUT.cphy_tx_fsm_U0.SerSeqSel == 0) &&
        (DUT.cphy_tx_fsm_U0.EncoderEn == 0) &&
        (DUT.cphy_tx_fsm_U0.TxReadyHS == 0) &&
        (DUT.cphy_tx_fsm_U0.TxReadyEsc == 0) &&
        (DUT.cphy_tx_fsm_U0.Direction == 0) &&
        (DUT.cphy_tx_fsm_U0.Stopstate == 0) &&
        (DUT.cphy_tx_fsm_U0.EscSerEn == 0) &&
        (DUT.cphy_tx_fsm_U0.EscSerSeqSel == 0) &&
        (DUT.cphy_tx_fsm_U0.EscEncoderEn == 1) &&
        (DUT.cphy_tx_fsm_U0.TxCtrlOut == 2'b01) &&
        (DUT.cphy_tx_fsm_U0.LpCtrlEscSel == 0) &&
        (DUT.cphy_tx_fsm_U0.LpTxEn == 1) &&
        (DUT.cphy_tx_fsm_U0.HsTxEn == 0) &&
        (DUT.cphy_tx_fsm_U0.LpRxEn == 1) &&
        (DUT.cphy_tx_fsm_U0.Timer_En == 1) &&
        (DUT.cphy_tx_fsm_U0.Timer_Seed == 0) &&
        (DUT.cphy_tx_fsm_U0.HsSeqCtr == 0)
        ); 
  endproperty
  property TX_HS_SYNC_WORD_P;
    @(posedge TxWordClkHs)
      disable iff (!RstN)
      (DUT.cphy_tx_fsm_U0.current_state == TX_HS_SYNC_WORD) |-> (
        (DUT.cphy_tx_fsm_U0.HsSerializerEn == 0) &&
        (DUT.cphy_tx_fsm_U0.SerSeqSel == 0) &&
        (DUT.cphy_tx_fsm_U0.EncoderEn == 1) &&
        (DUT.cphy_tx_fsm_U0.TxReadyEsc == 0) &&
        (DUT.cphy_tx_fsm_U0.Direction == 0) &&
        (DUT.cphy_tx_fsm_U0.Stopstate == 0) &&
        (DUT.cphy_tx_fsm_U0.EscSerEn == 0) &&
        (DUT.cphy_tx_fsm_U0.EscSerSeqSel == 0) &&
        (DUT.cphy_tx_fsm_U0.EscEncoderEn == 0) &&
        (DUT.cphy_tx_fsm_U0.TxCtrlOut == 2'b10) &&
        (DUT.cphy_tx_fsm_U0.LpCtrlEscSel == 0) &&
        (DUT.cphy_tx_fsm_U0.LpTxEn == 0) &&
        (DUT.cphy_tx_fsm_U0.HsTxEn == 1) &&
        (DUT.cphy_tx_fsm_U0.LpRxEn == 0) &&
        (DUT.cphy_tx_fsm_U0.Timer_En == 0) &&
        (DUT.cphy_tx_fsm_U0.Timer_Seed == 0) &&
        (DUT.cphy_tx_fsm_U0.HsSeqCtr == 3'b010)
        ); 
  endproperty
  property TX_TA_GO_P;
    @(posedge TxWordClkHs)
      disable iff (!RstN)
      (DUT.cphy_tx_fsm_U0.current_state == TX_TA_GO) |-> (
        (DUT.cphy_tx_fsm_U0.HsSerializerEn == 0) &&
        (DUT.cphy_tx_fsm_U0.SerSeqSel == 0) &&
        (DUT.cphy_tx_fsm_U0.EncoderEn == 0) &&
        (DUT.cphy_tx_fsm_U0.TxReadyHS == 0) &&
        (DUT.cphy_tx_fsm_U0.TxReadyEsc == 0) &&
        (DUT.cphy_tx_fsm_U0.Direction == 0) &&
        (DUT.cphy_tx_fsm_U0.Stopstate == 0) &&
        (DUT.cphy_tx_fsm_U0.EscSerEn == 0) &&
        (DUT.cphy_tx_fsm_U0.EscSerSeqSel == 0) &&
        (DUT.cphy_tx_fsm_U0.EscEncoderEn == 0) &&
        (DUT.cphy_tx_fsm_U0.TxCtrlOut == 2'b10) &&
        (DUT.cphy_tx_fsm_U0.LpCtrlEscSel == 0) &&
        (DUT.cphy_tx_fsm_U0.LpTxEn == 1) &&
        (DUT.cphy_tx_fsm_U0.HsTxEn == 0) &&
        (DUT.cphy_tx_fsm_U0.LpRxEn == 1) &&
        (DUT.cphy_tx_fsm_U0.Timer_En == 1) &&
        (DUT.cphy_tx_fsm_U0.Timer_Seed == 1) &&
        (DUT.cphy_tx_fsm_U0.HsSeqCtr == 0)
        ); 
  endproperty
  property TX_HS_SEND_DATA_P;
    @(posedge TxWordClkHs)
      disable iff (!RstN)
      (DUT.cphy_tx_fsm_U0.current_state == TX_HS_SEND_DATA) |-> (
        (DUT.cphy_tx_fsm_U0.HsSerializerEn == 1) &&
        (DUT.cphy_tx_fsm_U0.SerSeqSel == 1) &&
        (DUT.cphy_tx_fsm_U0.EncoderEn == 1) &&
        (DUT.cphy_tx_fsm_U0.TxReadyHS == 1) &&
        (DUT.cphy_tx_fsm_U0.TxReadyEsc == 0) &&
        (DUT.cphy_tx_fsm_U0.Direction == 0) &&
        (DUT.cphy_tx_fsm_U0.Stopstate == 0) &&
        (DUT.cphy_tx_fsm_U0.EscSerEn == 0) &&
        (DUT.cphy_tx_fsm_U0.EscSerSeqSel == 0) &&
        (DUT.cphy_tx_fsm_U0.EscEncoderEn == 0) &&
        (DUT.cphy_tx_fsm_U0.TxCtrlOut == 2'b10) &&
        (DUT.cphy_tx_fsm_U0.LpCtrlEscSel == 0) &&
        (DUT.cphy_tx_fsm_U0.LpTxEn == 0) &&
        (DUT.cphy_tx_fsm_U0.HsTxEn == 1) &&
        (DUT.cphy_tx_fsm_U0.LpRxEn == 0) &&
        (DUT.cphy_tx_fsm_U0.Timer_En == 0) &&
        (DUT.cphy_tx_fsm_U0.Timer_Seed == 0) &&
        (DUT.cphy_tx_fsm_U0.HsSeqCtr == 0)
        ); 
  endproperty
  property TX_HS_POST_P;
    @(posedge TxWordClkHs)
      disable iff (!RstN)
      (DUT.cphy_tx_fsm_U0.current_state == TX_HS_POST) |-> (
        (DUT.cphy_tx_fsm_U0.HsSerializerEn == 0) &&
        (DUT.cphy_tx_fsm_U0.SerSeqSel == 0) &&
        (DUT.cphy_tx_fsm_U0.EncoderEn == 1) &&
        (DUT.cphy_tx_fsm_U0.TxReadyHS == 0) &&
        (DUT.cphy_tx_fsm_U0.TxReadyEsc == 0) &&
        (DUT.cphy_tx_fsm_U0.Direction == 0) &&
        (DUT.cphy_tx_fsm_U0.Stopstate == 0) &&
        (DUT.cphy_tx_fsm_U0.EscSerEn == 0) &&
        (DUT.cphy_tx_fsm_U0.EscSerSeqSel == 0) &&
        (DUT.cphy_tx_fsm_U0.EscEncoderEn == 0) &&
        (DUT.cphy_tx_fsm_U0.TxCtrlOut == 2'b10) &&
        (DUT.cphy_tx_fsm_U0.LpCtrlEscSel == 0) &&
        (DUT.cphy_tx_fsm_U0.LpTxEn == 0) &&
        (DUT.cphy_tx_fsm_U0.HsTxEn == 1) &&
        (DUT.cphy_tx_fsm_U0.LpRxEn == 0) &&
        (DUT.cphy_tx_fsm_U0.Timer_En == 0) &&
        (DUT.cphy_tx_fsm_U0.Timer_Seed == 0) &&
        (DUT.cphy_tx_fsm_U0.HsSeqCtr == 1)
        ); 
  endproperty
  property RX_TA_LOOK_P;
    @(posedge TxWordClkHs)
      disable iff (!RstN)
      (DUT.cphy_tx_fsm_U0.current_state == RX_TA_LOOK) |-> (
        (DUT.cphy_tx_fsm_U0.HsSerializerEn == 0) &&
        (DUT.cphy_tx_fsm_U0.SerSeqSel == 0) &&
        (DUT.cphy_tx_fsm_U0.EncoderEn == 0) &&
        (DUT.cphy_tx_fsm_U0.TxReadyHS == 0) &&
        (DUT.cphy_tx_fsm_U0.TxReadyEsc == 0) &&
        (DUT.cphy_tx_fsm_U0.Direction == 1) &&
        (DUT.cphy_tx_fsm_U0.Stopstate == 0) &&
        (DUT.cphy_tx_fsm_U0.EscSerEn == 0) &&
        (DUT.cphy_tx_fsm_U0.EscSerSeqSel == 0) &&
        (DUT.cphy_tx_fsm_U0.EscEncoderEn == 0) &&
        (DUT.cphy_tx_fsm_U0.TxCtrlOut == 2'b00) &&
        (DUT.cphy_tx_fsm_U0.LpCtrlEscSel == 0) &&
        (DUT.cphy_tx_fsm_U0.LpTxEn == 0) &&
        (DUT.cphy_tx_fsm_U0.HsTxEn == 0) &&
        (DUT.cphy_tx_fsm_U0.LpRxEn == 1) &&
        (DUT.cphy_tx_fsm_U0.Timer_En == 0) &&
        (DUT.cphy_tx_fsm_U0.Timer_Seed == 0) &&
        (DUT.cphy_tx_fsm_U0.HsSeqCtr == 0)
        ); 
  endproperty
  property RX_TA_ACK_P;
    @(posedge TxWordClkHs)
      disable iff (!RstN)
      (DUT.cphy_tx_fsm_U0.current_state == RX_TA_ACK) |-> (
        (DUT.cphy_tx_fsm_U0.HsSerializerEn == 0) &&
        (DUT.cphy_tx_fsm_U0.SerSeqSel == 0) &&
        (DUT.cphy_tx_fsm_U0.EncoderEn == 0) &&
        (DUT.cphy_tx_fsm_U0.TxReadyHS == 0) &&
        (DUT.cphy_tx_fsm_U0.TxReadyEsc == 0) &&
        (DUT.cphy_tx_fsm_U0.Direction == 1) &&
        (DUT.cphy_tx_fsm_U0.Stopstate == 0) &&
        (DUT.cphy_tx_fsm_U0.EscSerEn == 0) &&
        (DUT.cphy_tx_fsm_U0.EscSerSeqSel == 0) &&
        (DUT.cphy_tx_fsm_U0.EscEncoderEn == 0) &&
        (DUT.cphy_tx_fsm_U0.TxCtrlOut == 2'b00) &&
        (DUT.cphy_tx_fsm_U0.LpCtrlEscSel == 0) &&
        (DUT.cphy_tx_fsm_U0.LpTxEn == 0) &&
        (DUT.cphy_tx_fsm_U0.HsTxEn == 0) &&
        (DUT.cphy_tx_fsm_U0.LpRxEn == 1) &&
        (DUT.cphy_tx_fsm_U0.Timer_En == 0) &&
        (DUT.cphy_tx_fsm_U0.Timer_Seed == 0) &&
        (DUT.cphy_tx_fsm_U0.HsSeqCtr == 0)
        ); 
  endproperty
  property FORCE_RX_P;
    @(posedge TxWordClkHs)
      disable iff (!RstN)
      (DUT.cphy_tx_fsm_U0.current_state == FORCE_RX) |-> (
        (DUT.cphy_tx_fsm_U0.HsSerializerEn == 0) &&
        (DUT.cphy_tx_fsm_U0.SerSeqSel == 0) &&
        (DUT.cphy_tx_fsm_U0.EncoderEn == 0) &&
        (DUT.cphy_tx_fsm_U0.TxReadyHS == 0) &&
        (DUT.cphy_tx_fsm_U0.TxReadyEsc == 0) &&
        (DUT.cphy_tx_fsm_U0.Direction == 1) &&
        (DUT.cphy_tx_fsm_U0.Stopstate == 0) &&
        (DUT.cphy_tx_fsm_U0.EscSerEn == 0) &&
        (DUT.cphy_tx_fsm_U0.EscSerSeqSel == 0) &&
        (DUT.cphy_tx_fsm_U0.EscEncoderEn == 0) &&
        (DUT.cphy_tx_fsm_U0.LpCtrlEscSel == 0) &&
        (DUT.cphy_tx_fsm_U0.LpTxEn == 0) &&
        (DUT.cphy_tx_fsm_U0.HsTxEn == 0) &&
        (DUT.cphy_tx_fsm_U0.LpRxEn == 1) &&
        (DUT.cphy_tx_fsm_U0.Timer_En == 0) &&
        (DUT.cphy_tx_fsm_U0.Timer_Seed == 0) &&
        (DUT.cphy_tx_fsm_U0.HsSeqCtr == 0)
        ); 
  endproperty
  property TX_ESC_GO_P;
    @(posedge TxWordClkHs)
      disable iff (!RstN)
      (DUT.cphy_tx_fsm_U0.current_state == TX_ESC_GO) |-> (
        (DUT.cphy_tx_fsm_U0.HsSerializerEn == 0) &&
        (DUT.cphy_tx_fsm_U0.SerSeqSel == 0) &&
        (DUT.cphy_tx_fsm_U0.EncoderEn == 0) &&
        (DUT.cphy_tx_fsm_U0.TxReadyHS == 0) &&
        (DUT.cphy_tx_fsm_U0.TxReadyEsc == 0) &&
        (DUT.cphy_tx_fsm_U0.Direction == 0) &&
        (DUT.cphy_tx_fsm_U0.Stopstate == 0) &&
        (DUT.cphy_tx_fsm_U0.EscSerEn == 0) &&
        (DUT.cphy_tx_fsm_U0.EscSerSeqSel == 0) &&
        (DUT.cphy_tx_fsm_U0.EscEncoderEn == 1) &&
        (DUT.cphy_tx_fsm_U0.TxCtrlOut == 2'b10) &&
        (DUT.cphy_tx_fsm_U0.LpCtrlEscSel == 0) &&
        (DUT.cphy_tx_fsm_U0.LpTxEn == 1) &&
        (DUT.cphy_tx_fsm_U0.HsTxEn == 0) &&
        (DUT.cphy_tx_fsm_U0.LpRxEn == 1) &&
        (DUT.cphy_tx_fsm_U0.Timer_En == 1) &&
        (DUT.cphy_tx_fsm_U0.Timer_Seed == 0) &&
        (DUT.cphy_tx_fsm_U0.HsSeqCtr == 0)
        ); 
  endproperty
  property TX_ESC_CMD_P;
    @(posedge TxWordClkHs)
      disable iff (!RstN)
      (DUT.cphy_tx_fsm_U0.current_state == TX_ESC_CMD) |-> (
        (DUT.cphy_tx_fsm_U0.HsSerializerEn == 0) &&
        (DUT.cphy_tx_fsm_U0.SerSeqSel == 0) &&
        (DUT.cphy_tx_fsm_U0.EncoderEn == 0) &&
        (DUT.cphy_tx_fsm_U0.TxReadyHS == 0) &&
        (DUT.cphy_tx_fsm_U0.TxReadyEsc == 0) &&
        (DUT.cphy_tx_fsm_U0.Direction == 0) &&
        (DUT.cphy_tx_fsm_U0.Stopstate == 0) &&
        (DUT.cphy_tx_fsm_U0.EscSerEn == 0) &&
        (DUT.cphy_tx_fsm_U0.EscSerSeqSel == 0) &&
        (DUT.cphy_tx_fsm_U0.EscEncoderEn == 1) &&
        (DUT.cphy_tx_fsm_U0.TxCtrlOut == 2'b00) &&
        (DUT.cphy_tx_fsm_U0.LpCtrlEscSel == 1) &&
        (DUT.cphy_tx_fsm_U0.LpTxEn == 1) &&
        (DUT.cphy_tx_fsm_U0.HsTxEn == 0) &&
        (DUT.cphy_tx_fsm_U0.LpRxEn == 1) &&
        (DUT.cphy_tx_fsm_U0.Timer_En == 0) &&
        (DUT.cphy_tx_fsm_U0.Timer_Seed == 0) &&
        (DUT.cphy_tx_fsm_U0.HsSeqCtr == 0)
        ); 
  endproperty
  property TX_LPDT_P;
    @(posedge TxWordClkHs)
      disable iff (!RstN)
      (DUT.cphy_tx_fsm_U0.current_state == TX_LPDT) |-> (
        (DUT.cphy_tx_fsm_U0.HsSerializerEn == 0) &&
        (DUT.cphy_tx_fsm_U0.SerSeqSel == 0) &&
        (DUT.cphy_tx_fsm_U0.EncoderEn == 0) &&
        (DUT.cphy_tx_fsm_U0.TxReadyHS == 0) &&
        (DUT.cphy_tx_fsm_U0.Direction == 0) &&
        (DUT.cphy_tx_fsm_U0.Stopstate == 0) &&
        (DUT.cphy_tx_fsm_U0.EscSerEn == 1) &&
        (DUT.cphy_tx_fsm_U0.EscSerSeqSel == 1) &&
        (DUT.cphy_tx_fsm_U0.EscEncoderEn == 1) &&
        (DUT.cphy_tx_fsm_U0.TxCtrlOut == 2'b00) &&
        (DUT.cphy_tx_fsm_U0.LpCtrlEscSel == 1) &&
        (DUT.cphy_tx_fsm_U0.LpTxEn == 1) &&
        (DUT.cphy_tx_fsm_U0.HsTxEn == 0) &&
        (DUT.cphy_tx_fsm_U0.LpRxEn == 1) &&
        (DUT.cphy_tx_fsm_U0.Timer_En == 0) &&
        (DUT.cphy_tx_fsm_U0.Timer_Seed == 0) &&
        (DUT.cphy_tx_fsm_U0.HsSeqCtr == 0)
        ); 
  endproperty
  property TX_TRIGGERS_P;
    @(posedge TxWordClkHs)
      disable iff (!RstN)
      (DUT.cphy_tx_fsm_U0.current_state == TX_TRIGGERS) |-> (
        (DUT.cphy_tx_fsm_U0.HsSerializerEn == 0) &&
        (DUT.cphy_tx_fsm_U0.SerSeqSel == 0) &&
        (DUT.cphy_tx_fsm_U0.EncoderEn == 0) &&
        (DUT.cphy_tx_fsm_U0.TxReadyHS == 0) &&
        (DUT.cphy_tx_fsm_U0.TxReadyEsc == 0) &&
        (DUT.cphy_tx_fsm_U0.Direction == 0) &&
        (DUT.cphy_tx_fsm_U0.Stopstate == 0) &&
        (DUT.cphy_tx_fsm_U0.EscSerEn == 0) &&
        (DUT.cphy_tx_fsm_U0.EscSerSeqSel == 0) &&
        (DUT.cphy_tx_fsm_U0.EscEncoderEn == 1) &&
        (DUT.cphy_tx_fsm_U0.TxCtrlOut == 2'b00) &&
        (DUT.cphy_tx_fsm_U0.LpCtrlEscSel == 1) &&
        (DUT.cphy_tx_fsm_U0.LpTxEn == 1) &&
        (DUT.cphy_tx_fsm_U0.HsTxEn == 0) &&
        (DUT.cphy_tx_fsm_U0.LpRxEn == 1) &&
        (DUT.cphy_tx_fsm_U0.Timer_En == 0) &&
        (DUT.cphy_tx_fsm_U0.Timer_Seed == 0) &&
        (DUT.cphy_tx_fsm_U0.HsSeqCtr == 0)
        ); 
  endproperty
  property TX_ULPS_P;
    @(posedge TxWordClkHs)
      disable iff (!RstN)
      (DUT.cphy_tx_fsm_U0.current_state == TX_ULPS) |-> (
        (DUT.cphy_tx_fsm_U0.HsSerializerEn == 0) &&
        (DUT.cphy_tx_fsm_U0.SerSeqSel == 0) &&
        (DUT.cphy_tx_fsm_U0.EncoderEn == 0) &&
        (DUT.cphy_tx_fsm_U0.TxReadyHS == 0) &&
        (DUT.cphy_tx_fsm_U0.TxReadyEsc == 0) &&
        (DUT.cphy_tx_fsm_U0.Direction == 0) &&
        (DUT.cphy_tx_fsm_U0.Stopstate == 0) &&
        (DUT.cphy_tx_fsm_U0.EscSerEn == 0) &&
        (DUT.cphy_tx_fsm_U0.EscSerSeqSel == 0) &&
        (DUT.cphy_tx_fsm_U0.EscEncoderEn == 1) &&
        (DUT.cphy_tx_fsm_U0.TxCtrlOut == 2'b00) &&
        (DUT.cphy_tx_fsm_U0.LpCtrlEscSel == 1) &&
        (DUT.cphy_tx_fsm_U0.LpTxEn == 1) &&
        (DUT.cphy_tx_fsm_U0.HsTxEn == 0) &&
        (DUT.cphy_tx_fsm_U0.LpRxEn == 1) &&
        (DUT.cphy_tx_fsm_U0.Timer_En == 0) &&
        (DUT.cphy_tx_fsm_U0.Timer_Seed == 0) &&
        (DUT.cphy_tx_fsm_U0.HsSeqCtr == 0)
        ); 
  endproperty
  property TX_LPDT_Pause_P;
    @(posedge TxWordClkHs)
      disable iff (!RstN)
      (DUT.cphy_tx_fsm_U0.current_state == TX_LPDT_Pause) |-> (
        (DUT.cphy_tx_fsm_U0.HsSerializerEn == 0) &&
        (DUT.cphy_tx_fsm_U0.SerSeqSel == 0) &&
        (DUT.cphy_tx_fsm_U0.EncoderEn == 0) &&
        (DUT.cphy_tx_fsm_U0.TxReadyHS == 0) &&
        (DUT.cphy_tx_fsm_U0.Direction == 0) &&
        (DUT.cphy_tx_fsm_U0.Stopstate == 0) &&
        (DUT.cphy_tx_fsm_U0.EscSerEn == 0) &&
        (DUT.cphy_tx_fsm_U0.EscSerSeqSel == 1) &&
        (DUT.cphy_tx_fsm_U0.EscEncoderEn == 1) &&
        (DUT.cphy_tx_fsm_U0.TxCtrlOut == 2'b00) &&
        (DUT.cphy_tx_fsm_U0.LpCtrlEscSel == 1) &&
        (DUT.cphy_tx_fsm_U0.LpTxEn == 1) &&
        (DUT.cphy_tx_fsm_U0.HsTxEn == 0) &&
        (DUT.cphy_tx_fsm_U0.LpRxEn == 1) &&
        (DUT.cphy_tx_fsm_U0.Timer_En == 0) &&
        (DUT.cphy_tx_fsm_U0.Timer_Seed == 0) &&
        (DUT.cphy_tx_fsm_U0.HsSeqCtr == 0)
        ); 
  endproperty

  assert property (TX_HS_REQUEST_P)
    else begin
      print_signals();
      $fatal("TX_HS_REQUEST state failure [%0t] \n", $time);
    end
  assert property (TX_LP_RQST_P)
      else begin
        print_signals();
        $fatal("TX_LP_RQST state failure [%0t] \n", $time);
      end
  assert property (TX_HS_PREPARE_P)
      else begin
        print_signals();
        $fatal("TX_HS_PREPARE state failure [%0t] \n", $time);
      end
  assert property (TX_LP_YIELD_P)
      else begin
        print_signals();
        $fatal("TX_LP_YIELD state failure [%0t] \n", $time);
      end
  assert property (TX_HS_PREAMBLE_P)
      else begin
        print_signals();
        $fatal("TX_HS_PREAMBLE state failure [%0t] \n", $time);
      end
  assert property (TX_TA_REQUEST_P)
      else begin
        print_signals();
        $fatal("TX_TA_REQUEST state failure [%0t] \n", $time);
      end
  assert property (TX_ESC_RQST_P)
      else begin
        print_signals();
        $fatal("TX_ESC_RQST state failure [%0t] \n", $time);
      end
  assert property (TX_HS_SYNC_WORD_P)
      else begin
        print_signals();
        $fatal("TX_HS_SYNC_WORD state failure [%0t] \n", $time);
      end
  assert property (TX_TA_GO_P)
      else begin
        print_signals();
        $fatal("TX_TA_GO state failure [%0t] \n", $time);
      end
  assert property (TX_HS_SEND_DATA_P)
      else begin
        print_signals();
        $fatal("TX_HS_SEND_DATA state failure [%0t] \n", $time);
      end
  assert property (TX_HS_POST_P)
      else begin
        print_signals();
        $fatal("TX_HS_POST state failure [%0t] \n", $time);
      end
  assert property (RX_TA_LOOK_P)
      else begin
        print_signals();
        $fatal("RX_TA_LOOK state failure [%0t] \n", $time);
      end
  assert property (RX_TA_ACK_P)
      else begin
        print_signals();
        $fatal("RX_TA_ACK state failure [%0t] \n", $time);
      end
  assert property (FORCE_RX_P)
      else begin
        print_signals();
        $fatal("FORCE_RX state failure [%0t] \n", $time);
      end
  assert property (TX_ESC_GO_P)
      else begin
        print_signals();
        $fatal("TX_ESC_GO state failure [%0t] \n", $time);
      end
  assert property (TX_ESC_CMD_P)
      else begin
        print_signals();
        $fatal("TX_ESC_CMD state failure [%0t] \n", $time);
      end
  assert property (TX_LPDT_P)
      else begin
        print_signals();
        $fatal("TX_LPDT state failure [%0t] \n", $time);
      end
  assert property (TX_TRIGGERS_P)
      else begin
        print_signals();
        $fatal("TX_TRIGGERS state failure [%0t] \n", $time);
      end
  assert property (TX_ULPS_P)
      else begin
        print_signals();
        $fatal("TX_ULPS state failure [%0t] \n", $time);
      end
  assert property (TX_LPDT_Pause_P)
      else begin
        print_signals();
        $fatal("TX_LPDT_Pause state failure [%0t] \n", $time);
      end
  
  /////////////////// Post Check  ///////////////////

    //Previous A,B,C values for output states checking
    reg [1:0] Not_A_Prev,Not_B_Prev,Not_C_Prev;

    always @(posedge TxSymbolClkHS) begin
      Not_A_Prev <= ~DUT.A_PU_PD;
      Not_B_Prev <= ~DUT.B_PU_PD;
      Not_C_Prev <= ~DUT.C_PU_PD;
    end

    property Post_Check;
    @(posedge TxSymbolClkHS)
      disable iff (!RstN || !DUT.cphy_tx_fsm_U0.EncoderEn)
      (DUT.cphy_tx_fsm_U0.current_state == 5'd11) |=> ##11 ((DUT.A_PU_PD == 2'd3)? ((DUT.B_PU_PD == Not_B_Prev) && (DUT.C_PU_PD == Not_C_Prev)) : 
                                                          ((DUT.B_PU_PD == 2'd3)? ((DUT.A_PU_PD == Not_A_Prev) && (DUT.C_PU_PD == Not_C_Prev)) :
                                                          ((DUT.A_PU_PD == Not_A_Prev) && (DUT.B_PU_PD == Not_B_Prev)))
                                                          ); 
    endproperty

    assert property (Post_Check)
    else $fatal("Post Error at Time [%0t] \n", $time);

  //====================================================================
  //========================== Test tasks ==============================
  //====================================================================


  //===============================================//
  //=================== TX Tasks ==================//
  //===============================================//

  task Initialize;
  begin
    TxDataHS = 16'b0;
    TxSendSyncHS = 1'b0;
    TxReqHS = 1'b0;
    TxReqEsc = 1'b0;
    TxLpdtEsc = 1'b0;
    TxUlpsEsc = 1'b0;
    TxUlpsExit = 1'b0;
    TxTriggerEsc = 4'b0;
    TxDataEsc = 8'b0;
    TxValidEsc = 1'b0;
    TurnRequest = 1'b0;
    TurnDisable = 1'b0;
    ForceRxmode = 1'b0;
    ForceTxStopmode = 1'b0;
    WaitHs = 1'b0;
    WaitEsc = 1'b0;
    WaitNotEsc = 1'b0;
  end
  endtask

  task Reset_Enable;
  begin
    RstN = 0; Enable = 0; #10;
    RstN = 1; Enable = 0; #10;
    Enable = 1;
  end
  endtask

  task Stop_Check;
  begin
    if (!TxReadyHS &&
        !TxReadyEsc && 
        LpRxEn &&
        !RxLpdtEsc && 
        !RxUlpsEsc && 
        !(|RxTriggerEsc) && 
        !Direction && 
        Stopstate && 
        UlpsActiveNot
      )
    begin
      $display("TX_Stop State Pass! [%0t]\n", $time);
    end
    else begin
      $display("TX_Stop State Fail! [%0t]\n", $time);
      $display("Signal dump:");
      $display("  TxReadyHS         = %b", TxReadyHS);
      $display("  TxReadyEsc        = %b", TxReadyEsc);
      $display("  LpRxEn            = %b", LpRxEn);
      $display("  RxLpdtEsc         = %b", RxLpdtEsc);
      $display("  RxUlpsEsc         = %b", RxUlpsEsc);
      $display("  RxTriggerEsc      = %b", RxTriggerEsc);
      $display("  Direction         = %b", Direction);
      $display("  Stopstate         = %b", Stopstate);
      $display("  UlpsActiveNot     = %b", UlpsActiveNot);
    end
  end
  endtask


  task Rx_Stop_Check;
    begin
      if (!TxReadyHS && 
          !TxReadyEsc && 
          LpRxEn &&
          !RxLpdtEsc && 
          !RxUlpsEsc && 
          !(|RxTriggerEsc) && 
          Direction && 
          Stopstate && 
          UlpsActiveNot)

      $display("RX_Stop State Pass! [%0t] \n", $time);
      else begin
      $display("RX_Stop State Fail! [%0t] \n", $time);
      $display("Signal dump:");
      $display("  TxReadyHS         = %b", TxReadyHS);
      $display("  TxReadyEsc        = %b", TxReadyEsc);
      $display("  LpRxEn            = %b", LpRxEn);
      $display("  RxLpdtEsc         = %b", RxLpdtEsc);
      $display("  RxUlpsEsc         = %b", RxUlpsEsc);
      $display("  RxTriggerEsc      = %b", RxTriggerEsc);
      $display("  Direction         = %b", Direction);
      $display("  Stopstate         = %b", Stopstate);
      $display("  UlpsActiveNot     = %b", UlpsActiveNot);
      end
    end
  endtask

  task Ulps_Check;
    begin
      if (!TxReadyHS && 
          !TxReadyEsc && 
          !RxLpdtEsc && 
          !RxUlpsEsc && 
          !(|RxTriggerEsc) && 
          !Direction && 
          !Stopstate && 
          !UlpsActiveNot
        )
      $display("Ulps State Pass! [%0t] \n", $time);
      else begin
      $display("Ulps State Fail! [%0t] \n", $time);
      $display("Signal dump:");
      $display("  TxReadyHS         = %b", TxReadyHS);
      $display("  TxReadyEsc        = %b", TxReadyEsc);
      $display("  LpRxEn            = %b", LpRxEn);
      $display("  RxLpdtEsc         = %b", RxLpdtEsc);
      $display("  RxUlpsEsc         = %b", RxUlpsEsc);
      $display("  RxTriggerEsc      = %b", RxTriggerEsc);
      $display("  Direction         = %b", Direction);
      $display("  Stopstate         = %b", Stopstate);
      $display("  UlpsActiveNot     = %b", UlpsActiveNot);
      end
    end
  endtask

  task Wait_ReadyHs(input string Ready_Number);
    begin
      Ready_Num = Ready_Number;
      WaitHs = 1'b1;
      @(posedge TxWordClkHs)
      #0.1;
      WaitHs = 1'b0;
      wait (TxReadyHS == 1);
    end
  endtask

  task Wait_ReadyEsc(input string Ready_Number);
    begin
      Ready_Num = Ready_Number;
      WaitEsc = 1'b1;
      @(posedge TxWordClkHs)
      #0.1;
      WaitEsc = 1'b0;
      wait (TxReadyEsc == 1);
    end
  endtask

  task Wait_NotReadyEsc(input string Ready_Number);
    begin
      Ready_Num = Ready_Number;
      WaitNotEsc = 1'b1;
      @(posedge TxWordClkHs)
      #0.1;
      WaitNotEsc = 1'b0;
      wait (TxReadyEsc == 0);
    end
  endtask

  task Basic_HS_transmission;
    $display("Running Basic HS transmission...");
    begin
    TxReqHS = 1;
    TxDataHS = 16'hABCD;
    TxSendSyncHS = 0;
    
    Wait_ReadyHs("1");
    Check_State(TX_HS_SEND_DATA);

    #10;
    TxReqHS = 0;
    #100;
    end
    endtask

    task HS_continuous_data;
    begin
    $display("Running HS continuous data...");
    TxReqHS = 1;
    TxDataHS = $random;
    Wait_ReadyHs("2");
    Check_State(TX_HS_SEND_DATA);
    repeat (5) begin
      TxDataHS = $random;
      @(posedge TxWordClkHs);
    end
    TxReqHS = 0;
    #125;
    end
    endtask
    
    task HS_word_sync_transmission;
    begin
    $display("Running HS word sync transmission...");
    TxReqHS = 1;
    TxDataHS = $random;
    Wait_ReadyHs("3");

    //Send two words
    repeat (2) begin
      TxDataHS = $random;
      @(posedge TxWordClkHs);
    end
    
    @(posedge TxWordClkHs);
    TxDataHS = $random;

    Check_State(TX_HS_SEND_DATA);
    //Sync Request
    @(posedge TxWordClkHs);
    TxSendSyncHS = 1;
    TxDataHS = 16'hAB66;
    $display("TxSendSyncHS asserted! [%0t] \n", $time);
    @(posedge TxWordClkHs);
    TxSendSyncHS = 0;
    TxDataHS = 16'hAB66;
    $display("TxSendSyncHS deasserted! [%0t] \n", $time);
    @(posedge TxWordClkHs);
    Check_State(TX_HS_SYNC_WORD);
    TxDataHS = $random;
    @(posedge TxWordClkHs);
    TxDataHS = $random;
    @(posedge TxWordClkHs);
    #1;
    @(posedge TxWordClkHs);
    //Send two words
    repeat (2) begin
      TxDataHS = $random;
      @(posedge TxWordClkHs);
    end
    #10;
    TxReqHS = 0;
    #120;
    end
    endtask

    task Valid_LPDT_data_transmission;
    begin
    $display("Running Valid LPDT data transmission...");
    TxReqEsc = 1;
    TxLpdtEsc = 1;
    TxValidEsc = 1;
    TxDataEsc = 8'b01110101;
    Wait_ReadyEsc("1");
    Check_State(TX_LPDT);
    @ (posedge TxClkEsc);
    TxValidEsc = 0;
    Wait_NotReadyEsc("1");
    Wait_ReadyEsc("2");
    @ (posedge TxClkEsc);
    @ (posedge TxClkEsc);
    @ (posedge TxClkEsc);
    TxValidEsc = 1;
    TxDataEsc = 8'b11010000;
    @ (posedge TxClkEsc);
    Wait_NotReadyEsc("1");
    TxValidEsc = 0;
    @ (posedge TxClkEsc);
    @ (posedge TxClkEsc);
    @ (posedge TxClkEsc);
    @ (posedge TxClkEsc);
    @ (posedge TxClkEsc);
    TxReqEsc = 0; TxLpdtEsc = 0;
    #850;
    end
    endtask

    task Multiple_LPDT_bytes;
    begin
    $display("Running Multiple LPDT bytes...");
    TxReqEsc = 1;
    TxLpdtEsc = 1;
    TxValidEsc = 1;
    TxDataEsc = 8'h55;
    Wait_ReadyEsc("3");
    Check_State(TX_LPDT);
    @ (posedge TxClkEsc);
    Wait_ReadyEsc("3");
    @(posedge TxClkEsc);
    @(posedge TxClkEsc);
    @(posedge TxClkEsc);
    @(posedge TxClkEsc);
    @(posedge TxClkEsc);
    @(posedge TxClkEsc);
    @(posedge TxClkEsc);
    @(posedge TxClkEsc);
    @(posedge TxClkEsc);
    @(posedge TxClkEsc);
    TxValidEsc = 1;
    TxDataEsc = 8'h45;
    Wait_ReadyEsc("5");
    Check_State(TX_LPDT);
    @ (posedge TxClkEsc);
    TxValidEsc = 0;
    #1000;
    TxReqEsc = 0; TxLpdtEsc = 0;
    #600;
    end
    endtask

    task No_TxValidEsc_asserted;
    begin
    $display("Running No TxValidEsc asserted...");
    TxReqEsc = 1; TxLpdtEsc = 1;
    Wait_ReadyEsc("8");
    #1;
    Check_State(TX_LPDT_Pause);
    #999;
    TxReqEsc = 0; TxLpdtEsc = 0;
    #600;
    end
    endtask
    
    task Enter_ULPS_mode;
    begin
    $display("Running Enter ULPS mode...");
    TxReqEsc = 1; TxUlpsEsc = 1;
    #1300;
    Ulps_Check();
    TxReqEsc = 0; TxUlpsEsc = 0;
    #500;
    end
    endtask

    task Exit_ULPS_mode;
    begin
    $display("Running Exit ULPS mode...");
    #300;
    TxUlpsExit = 1;
    #10;
    TxUlpsExit = 0;
    #300;
    end
    endtask

    task Reset_Trigger;
    begin
    $display("Running Reset Trigger...");
    TxReqEsc = 1; TxTriggerEsc = 4'b0001;
    #1400;
    Check_State(TX_TRIGGERS);
    TxReqEsc = 0; TxTriggerEsc = 0;
    #500;
    end
    endtask

    task TX_to_RX_Turnaround;
    begin
    $display("Running TX to RX Turnaround...");
    LpRx = 3'b000;
    TurnRequest = 1;
    #360;
    LpRx = 3'b100;
    #50;
    LpRx = 3'b111;
    #10;
    TurnRequest = 0;
    #110;
    end
    endtask

    task Force_TxStopmode;
    begin
    $display("Running Force TxStopmode...");
    ForceTxStopmode = 1;
    #20;
    ForceTxStopmode = 0;
    #110;
    end
    endtask

    task TX_to_RX_with_TurnDisable;
    begin
    $display("Running TX to RX with TurnDisable...");
    TurnDisable = 1;
    TurnRequest = 1;
    #230;
    LpRx = 3'b100;
    #50;
    LpRx = 3'b111;
    #10;
    TurnRequest = 0;
    #50;
    TurnDisable = 0;
    #100;
    end
    endtask

    task Force_RxMode;
    begin
    $display("Running Force RxMode...");
    ForceRxmode = 1;
    #20;
    ForceRxmode = 0;
    LpRx = 3'b111;
    #110;
    end
    endtask


    task Check_State(input logic [5:0] expected_state); 
    begin
        if (expected_state === DUT.cphy_tx_fsm_U0.current_state) begin
            $display("PASS: State matched. Expected = %0d, Actual = %0d", expected_state, DUT.cphy_tx_fsm_U0.current_state);
        end else begin
            $display("FAIL: State mismatch! Expected = %0d, Actual = %0d", expected_state, DUT.cphy_tx_fsm_U0.current_state);
        end
    end
    endtask


    //===============================================//
    //=================== RX Tasks ==================//
    //===============================================//
    
    task RX_STOP;
    begin 
        $display("[%0t] Applying RX_STOP", $time);
        LpRx[2]= 1; LpRx[1]= 1; LpRx[0]= 1;
        #(25);
        $display("[%0t] RX_STOP released", $time);
    end
    endtask  
      
    task Hs_Request;
    begin 
        $display("[%0t] Applying Hs_Request", $time);
        LpRx[2]= 0; LpRx[1]= 0; LpRx[0]= 1;
        #(25);
        LpRx[2]= 0; LpRx[1]= 0; LpRx[0]= 0;
        #(25);
        $display("[%0t] Hs_Request released", $time);
    end
    endtask
    
    task Preamble;
    begin
      $display("[%0t] Applying Preamble", $time);
       LpRx[2]= 1; LpRx[1]= 0;  LpRx[0]= 0;  // +x
       #2                           
       LpRx[2]= 1; LpRx[1]= 0;  LpRx[0]= 1;  // -y
       #2  
       LpRx[2]= 0; LpRx[1]= 0;  LpRx[0]= 1;  // +z
       #2
       LpRx[2]= 0; LpRx[1]= 1;  LpRx[0]= 1;  // -x
       #2
       LpRx[2]= 0; LpRx[1]= 1;  LpRx[0]= 0;  // +y
       #2
       LpRx[2]= 1; LpRx[1]= 1;  LpRx[0]= 0;  // -z
       #2
       LpRx[2]= 1; LpRx[1]= 0;  LpRx[0]= 0;  // +x
       #2
       LpRx[2]= 1; LpRx[1]= 0;  LpRx[0]= 1;  // -y
       #2  
       LpRx[2]= 0; LpRx[1]= 0;  LpRx[0]= 1;  // +z
       #2
       LpRx[2]= 0; LpRx[1]= 1;  LpRx[0]= 1;  // -x
       #2
       LpRx[2]= 0; LpRx[1]= 1;  LpRx[0]= 0;  // +y
       #2
       LpRx[2]= 1; LpRx[1]= 1;  LpRx[0]= 0;  // -z
       #2
       $display("[%0t] Preamble released", $time);
    end
    endtask

    task SyncWord;
    begin
       $display("[%0t] Applying SyncWord", $time);
       LpRx[2]= 1; LpRx[1]= 0;  LpRx[0]= 0;  // +x
       #2   
       LpRx[2]= 0; LpRx[1]= 1;  LpRx[0]= 1;  // -x
       #2   
       LpRx[2]= 1; LpRx[1]= 0;  LpRx[0]= 0;  // +x
       #2   
       LpRx[2]= 0; LpRx[1]= 1;  LpRx[0]= 1;  // -x
       #2   
       LpRx[2]= 1; LpRx[1]= 0;  LpRx[0]= 0;  // +x
       #2   
       LpRx[2]= 0; LpRx[1]= 1;  LpRx[0]= 1;  // -x
       #2   
       LpRx[2]= 0; LpRx[1]= 1;  LpRx[0]= 0;  // +y
       #2   
      $display("[%0t] SyncWord released", $time);
    end
    endtask

    task Data;
    begin
       $display("[%0t] Applying Data", $time);
       LpRx[2]= 0; LpRx[1]= 0;  LpRx[0]= 1;  // +z
       #2
       LpRx[2]= 0; LpRx[1]= 1;  LpRx[0]= 0;  // +y
       #2
       LpRx[2]= 1; LpRx[1]= 0;  LpRx[0]= 0;  // +x
       #2
       LpRx[2]= 0; LpRx[1]= 1;  LpRx[0]= 1;  // -x
       #2
       LpRx[2]= 1; LpRx[1]= 1;  LpRx[0]= 0;  // -z
       #2
       LpRx[2]= 0; LpRx[1]= 1;  LpRx[0]= 0;  // +y
       #2
      $display("[%0t] Data released", $time);
    end
    endtask

    task Post;
    begin
       $display("[%0t] Applying Post", $time);
       LpRx[2]= 1; LpRx[1]= 0;  LpRx[0]= 1;  // -y
       #2 
       LpRx[2]= 0; LpRx[1]= 1;  LpRx[0]= 0;  // +y
       #2
       LpRx[2]= 1; LpRx[1]= 0;  LpRx[0]= 1;  // -y
       #2
       LpRx[2]= 0; LpRx[1]= 1;  LpRx[0]= 0;  // +y
       #2
       LpRx[2]= 1; LpRx[1]= 0;  LpRx[0]= 1;  // -y
       #2
       LpRx[2]= 0; LpRx[1]= 1;  LpRx[0]= 0;  // +y
       #2
       LpRx[2]= 1; LpRx[1]= 0;  LpRx[0]= 1;  // -y
       #2
       $display("[%0t] Post released", $time);
    end
    endtask
    
   
    task LpRequest; 
    begin
        $display("[%0t] Applying LpRequest", $time);
        LpRx[2]= 1; LpRx[1]= 0; LpRx[0]= 0;
        #(25)
        LpRx[2]= 0; LpRx[1]= 0; LpRx[0]= 0;
        #(25)
        $display("[%0t] LpRequest released", $time);
    end
    endtask 

    task EscapeEntry; 
    begin
        $display("[%0t] Applying EscapeEntry", $time);
        LpRx[2]= 0; LpRx[1]= 0; LpRx[0]= 1;
        #(25)
        LpRx[2]= 0; LpRx[1]= 0; LpRx[0]= 0;
        #(25)
        $display("[%0t] EscapeEntry released", $time);
    end
    endtask 
    
    reg [7:0] comma = 8'b11100001;
    integer i;
    
    task CommandSend;
    begin
        $display("[%0t] Applying CommandSend", $time);
        for (i=7; i>=0; i=i-1)
        begin
        LpRx[2]=  comma [i];
        LpRx[0]= ~comma [i];
        #(25);
        LpRx[2]= 0; LpRx[1]= 0; LpRx[0]= 0;
        #(25);
        end
        $display("[%0t] CommandSend released", $time);
    end
    endtask

    task LpData;
    begin
        $display("[%0t] Applying LpData", $time);
        LpRx[2]= 1; LpRx[1]= 0; LpRx[0]= 0; 
        #(25);
        LpRx[2]= 0; LpRx[1]= 0; LpRx[0]= 0;
        #(25);
        LpRx[2]= 0; LpRx[1]= 0; LpRx[0]= 1; 
        #(25);
        LpRx[2]= 0; LpRx[1]= 0; LpRx[0]= 0;
        #(25); 
        LpRx[2]= 1; LpRx[1]= 0; LpRx[0]= 0; 
        #(25);
        LpRx[2]= 0; LpRx[1]= 0; LpRx[0]= 0;
        #(25); 
        LpRx[2]= 1; LpRx[1]= 0; LpRx[0]= 0; 
        #(25);
        LpRx[2]= 0; LpRx[1]= 0; LpRx[0]= 0;
        #(25);
        LpRx[2]= 0; LpRx[1]= 0; LpRx[0]= 1; 
        #(25);
        LpRx[2]= 0; LpRx[1]= 0; LpRx[0]= 0;
        #(25);
        LpRx[2]= 1; LpRx[1]= 0; LpRx[0]= 0; 
        #(25);
        LpRx[2]= 0; LpRx[1]= 0; LpRx[0]= 0;
        #(25);
        LpRx[2]= 1; LpRx[1]= 0; LpRx[0]= 0; 
        #(25);
        LpRx[2]= 0; LpRx[1]= 0; LpRx[0]= 0; 
        #(25); 
        LpRx[2]= 1; LpRx[1]= 0; LpRx[0]= 0; 
        #(25);
        LpRx[2]= 0; LpRx[1]= 0; LpRx[0]= 0; 
        #(25);
        $display("[%0t] LpData released", $time);       
    end
    endtask
    
    task space;
    begin
    $display("[%0t] Applying space", $time);
    repeat(5)
    begin
       LpRx[2]= 0; LpRx[1]= 0; LpRx[0]= 0;
       #(25);
    end
    $display("[%0t] space released", $time);
    end
    endtask
    
    task EndEscape;
    begin
        $display("[%0t] Applying EndEscape", $time);  
        LpRx[2]= 1; LpRx[1]= 0; LpRx[0]= 0; 
        #(25);
        LpRx[2]= 1; LpRx[1]= 1; LpRx[0]= 1;
        #(25);
        $display("[%0t] EndEscape released", $time);
    end
    endtask
    
    
    task Turnaround; 
    begin
        $display("[%0t] Applying Turnaround", $time);
        LpRx[2]= 1; LpRx[1]= 0; LpRx[0]= 0;
        #(25)
        LpRx[2]= 0; LpRx[1]= 0; LpRx[0]= 0;
        #(25)
        $display("[%0t] Turnaround released", $time);
    end
    endtask 

    task automatic assert_Lp_state(input [4:0] expected_state, input string message);
        if (DUT.cphy_tx_fsm_U0.current_state !== expected_state) begin
            $error("[FAIL] State mismatch! Expected: %d, Got: %d  | %s",
                  expected_state ,
                  DUT.cphy_tx_fsm_U0.current_state, message);
        end
        else begin
            $display("[PASS] State: %d - %s", expected_state , message);
            get_Lp_state_name(expected_state);
        end
    endtask
    
    task automatic get_Lp_state_name (input [4:0] state);
        case (state)
           DUT.cphy_tx_fsm_U0.RX_STOP              :
           begin
            assert_RX_STOP();     
           end
           DUT.cphy_tx_fsm_U0.RX_LP_YIELD           :
           begin
            assert_RX_LP_RQST();
           end
           DUT.cphy_tx_fsm_U0.RX_TA_WAIT           :
           begin
            assert_RX_TA_RQST();
           end
           DUT.cphy_tx_fsm_U0.TX_TA_GET            :
           begin
            assert_TX_TA_GET();
           end
           DUT.cphy_tx_fsm_U0.TX_TA_ACK            :
           begin
            assert_TX_TA_ACK();
           end
           DUT.cphy_tx_fsm_U0.TX_STOP              :
           begin
            assert_TX_STOP();
           end
           DUT.cphy_tx_fsm_U0.RX_Esc_Go            :
           begin
            assert_RX_ESC_RQST();
           end
           DUT.cphy_tx_fsm_U0.RX_ESC_CMD           :
           begin
            assert_RX_ESC_CMD();
           end
           DUT.cphy_tx_fsm_U0.RX_ULPS              :
           begin
           assert_RX_ULPS();
           end
           DUT.cphy_tx_fsm_U0.RX_ULPS_T_WAKE_UP    :
           begin
            assert_RX_ULPS_T_WAKE_UP();
           end
           DUT.cphy_tx_fsm_U0.RX_LPDT              :
           begin
            assert_RX_LPDT();
           end
           DUT.cphy_tx_fsm_U0.RX_WAIT              :
           begin
            assert_RX_WAIT();
           end
        endcase 
    endtask

    // Assertion tasks
    task assert_reset_values; // Like stop_state
    begin
        $display("[%0t] Checking reset values", $time);
        assert (DUT.cphy_tx_fsm_U0.LpRxEn          === 1) else  $error("LpRxEn not 1 during reset");
        assert (DUT.cphy_tx_fsm_U0.EscDecoderEn    === 0) else  $error("EscDecoderEn not 0 during reset");
        assert (DUT.cphy_tx_fsm_U0.CtrlDecoderEn   === 1) else  $error("CtrlDecoderEn not 1 during reset");
        assert (DUT.cphy_tx_fsm_U0.Stopstate       === 1) else  $error("Stopstate not 1 during reset");
        assert (DUT.cphy_tx_fsm_U0.Direction       === 1) else  $error("Direction not 1 during reset"); // Default to RX
        assert (DUT.cphy_tx_fsm_U0.UlpsActiveNot   === 1) else  $error("UlpsActiveNot not 1 during reset"); // Default to RX
		// LP PPI Signals
        assert (DUT.cphy_tx_fsm_U0.RxClkEsc     === DUT.RxClkEsc      ) else $error("RxClkEsc     not asserted in reset state");   
        assert (DUT.cphy_tx_fsm_U0.RxTriggerEsc === DUT.RxTriggerEsc) else $error("RxTriggerEsc not asserted in reset state");
        assert (DUT.cphy_tx_fsm_U0.RxUlpsEsc    === DUT.RxUlpsEsc   ) else $error("RxUlpsEsc    not asserted in reset state");
        assert (DUT.cphy_tx_fsm_U0.RxLpdtEsc    === DUT.RxLpdtEsc   ) else $error("RxLpdtEsc    not asserted in reset state");
		// LP Errors
        assert (DUT.cphy_tx_fsm_U0.ErrEsc     === DUT.ErrEsc    ) else $error("ErrEsc     not asserted in reset state"); 
        $display("[%0t] Reset values OK", $time);
    end
    endtask
	
	//===================================================================================================
	//================================================ RX ===============================================
	//===================================================================================================
	
	//===================================================================================================
	//========================================= LP FSM Assertion Tasks ==================================
	//===================================================================================================
    task assert_RX_STOP; 
    begin
        $display("[%0t] Checking RX_STOP values", $time);
        
        assert (DUT.cphy_tx_fsm_U0.LpRxEn          === 1) else  $error("LpRxEn          not 1 during RX_STOP");
        assert (DUT.cphy_tx_fsm_U0.EscDecoderEn    === 0) else  $error("EscDecoderEn    not 0 during RX_STOP");
        assert (DUT.cphy_tx_fsm_U0.CtrlDecoderEn   === 1) else  $error("CtrlDecoderEn   not 1 during RX_STOP");
        assert (DUT.cphy_tx_fsm_U0.Stopstate       === 1) else  $error("Stopstate       not 1 during RX_STOP");
        assert (DUT.cphy_tx_fsm_U0.Direction       === 1) else  $error("Direction       not 1 during RX_STOP"); // Default to RX
        assert (DUT.cphy_tx_fsm_U0.UlpsActiveNot   === 1) else  $error("UlpsActiveNot   not 1 during RX_STOP"); // Default to RX
		// LP PPI Signals
        assert (DUT.cphy_tx_fsm_U0.RxClkEsc     === DUT.RxClkEsc      ) else $error("RxClkEsc     not asserted in RX_STOP state");
        assert (DUT.cphy_tx_fsm_U0.RxTriggerEsc === DUT.RxTriggerEsc) else $error("RxTriggerEsc not asserted in RX_STOP state");
        assert (DUT.cphy_tx_fsm_U0.RxUlpsEsc    === DUT.RxUlpsEsc   ) else $error("RxUlpsEsc    not asserted in RX_STOP state");
        assert (DUT.cphy_tx_fsm_U0.RxLpdtEsc    === DUT.RxLpdtEsc   ) else $error("RxLpdtEsc    not asserted in RX_STOP state");
		// LP Errors
        assert (DUT.cphy_tx_fsm_U0.ErrEsc     === DUT.ErrEsc    ) else $error("ErrEsc     not asserted in RX_STOP state");
        $display("[%0t] RX_STOP values OK", $time);
    end
    endtask
	
    task assert_RX_LP_RQST; 
    begin
        $display("[%0t] Checking RX_LP_RQST values", $time);
        
        assert (DUT.cphy_tx_fsm_U0.Stopstate       === 0) else  $error("Stopstate not 0 during RX_LP_RQST");
		// LP PPI Signals
        assert (DUT.cphy_tx_fsm_U0.RxClkEsc     === DUT.RxClkEsc      ) else $error("RxClkEsc     not asserted in RX_LP_RQST state");
        assert (DUT.cphy_tx_fsm_U0.RxTriggerEsc === DUT.RxTriggerEsc) else $error("RxTriggerEsc not asserted in RX_LP_RQST state");
        assert (DUT.cphy_tx_fsm_U0.RxUlpsEsc    === DUT.RxUlpsEsc   ) else $error("RxUlpsEsc    not asserted in RX_LP_RQST state");
        assert (DUT.cphy_tx_fsm_U0.RxLpdtEsc    === DUT.RxLpdtEsc   ) else $error("RxLpdtEsc    not asserted in RX_LP_RQST state");
		// LP Errors
        assert (DUT.cphy_tx_fsm_U0.ErrEsc     === DUT.ErrEsc    ) else $error("ErrEsc     not asserted in RX_LP_RQST state"); 
        $display("[%0t] RX_LP_RQST values OK", $time);
    end
    endtask
	
    task assert_RX_TA_RQST; 
    begin
        $display("[%0t] Checking RX_TA_RQST values", $time);
		
        assert (DUT.cphy_tx_fsm_U0.Stopstate === 0)      else  $error("Stopstate not 0 during RX_TA_RQST");
        assert (DUT.cphy_tx_fsm_U0.RxTimerEn   === 1)      else  $error("RxTimerEn   not 1 during RX_TA_RQST");
        assert (DUT.cphy_tx_fsm_U0.RxTimerSeed === 3'b011) else  $error("RxTimerSeed not 3'b011 during RX_TA_RQST");
		// LP PPI Signals
        assert (DUT.cphy_tx_fsm_U0.RxClkEsc     === DUT.RxClkEsc      ) else $error("RxClkEsc     not asserted in RX_TA_RQST state");  
        assert (DUT.cphy_tx_fsm_U0.RxTriggerEsc === DUT.RxTriggerEsc) else $error("RxTriggerEsc not asserted in RX_TA_RQST state");
        assert (DUT.cphy_tx_fsm_U0.RxUlpsEsc    === DUT.RxUlpsEsc   ) else $error("RxUlpsEsc    not asserted in RX_TA_RQST state");
        assert (DUT.cphy_tx_fsm_U0.RxLpdtEsc    === DUT.RxLpdtEsc   ) else $error("RxLpdtEsc    not asserted in RX_TA_RQST state");
		// LP Errors
        assert (DUT.cphy_tx_fsm_U0.ErrEsc     === DUT.ErrEsc    ) else $error("ErrEsc     not asserted in RX_TA_RQST state");  
        $display("[%0t] RX_TA_RQST values OK", $time);
    end
    endtask
	
    task assert_TX_TA_GET; 
    begin
        $display("[%0t] Checking TX_TA_GET values", $time);
        
        assert (DUT.cphy_tx_fsm_U0.Stopstate     === 0     ) else  $error("Stopstate     not 0      during TX_TA_GET");
        assert (DUT.cphy_tx_fsm_U0.Direction     === 0     ) else  $error("Direction     not 0      during TX_TA_GET");
        assert (DUT.cphy_tx_fsm_U0.LpTxEn        === 1     ) else  $error("LpTxEn        not 1      during TX_TA_GET");
        assert (DUT.cphy_tx_fsm_U0.CtrlDecoderEn === 1     ) else  $error("CtrlDecoderEn not 1      during TX_TA_GET");
        assert (DUT.cphy_tx_fsm_U0.TxCtrlOut     === 2'b10 ) else  $error("TXCtrlOut     not 2'b10  during TX_TA_GET");
        assert (DUT.cphy_tx_fsm_U0.RxTimerEn       === 1     ) else  $error("RxTimerEn       not 1      during TX_TA_GET");
        assert (DUT.cphy_tx_fsm_U0.RxTimerSeed     === 3'b100) else  $error("RxTimerSeed     not 3'b100 during TX_TA_GET");
		// LP PPI Signals
        assert (DUT.cphy_tx_fsm_U0.RxClkEsc     === DUT.RxClkEsc      ) else $error("RxClkEsc     not asserted in TX_TA_GET state"); 
        assert (DUT.cphy_tx_fsm_U0.RxTriggerEsc === DUT.RxTriggerEsc) else $error("RxTriggerEsc not asserted in TX_TA_GET state");
        assert (DUT.cphy_tx_fsm_U0.RxUlpsEsc    === DUT.RxUlpsEsc   ) else $error("RxUlpsEsc    not asserted in TX_TA_GET state");
        assert (DUT.cphy_tx_fsm_U0.RxLpdtEsc    === DUT.RxLpdtEsc   ) else $error("RxLpdtEsc    not asserted in TX_TA_GET state");
		// LP Errors
        assert (DUT.cphy_tx_fsm_U0.ErrEsc     === DUT.ErrEsc    ) else $error("ErrEsc     not asserted in TX_TA_GET state"); 
        $display("[%0t] TX_TA_GET values OK", $time);
    end
    endtask
	
    task assert_TX_TA_ACK; 
    begin
        $display("[%0t] Checking TX_TA_ACK values", $time);
        
        assert (DUT.cphy_tx_fsm_U0.Stopstate     === 0     ) else  $error("Stopstate     not 0      during TX_TA_ACK");
        assert (DUT.cphy_tx_fsm_U0.Direction     === 0     ) else  $error("Direction     not 0      during TX_TA_ACK");
        assert (DUT.cphy_tx_fsm_U0.LpTxEn        === 1     ) else  $error("LpTxEn        not 1      during TX_TA_ACK");
        assert (DUT.cphy_tx_fsm_U0.CtrlDecoderEn === 1     ) else  $error("CtrlDecoderEn not 1      during TX_TA_ACK");
        assert (DUT.cphy_tx_fsm_U0.TxCtrlOut     === 2'b01 ) else  $error("TXCtrlOut     not 2'b01  during TX_TA_ACK");
        assert (DUT.cphy_tx_fsm_U0.RxTimerEn       === 1     ) else  $error("RxTimerEn       not 1      during TX_TA_ACK");
        assert (DUT.cphy_tx_fsm_U0.RxTimerSeed     === 3'b000) else  $error("RxTimerSeed     not 3'b000 during TX_TA_ACK");
		// LP PPI Signals
        assert (DUT.cphy_tx_fsm_U0.RxClkEsc     === DUT.RxClkEsc      ) else $error("RxClkEsc     not asserted in TX_TA_ACK state");   
        assert (DUT.cphy_tx_fsm_U0.RxTriggerEsc === DUT.RxTriggerEsc) else $error("RxTriggerEsc not asserted in TX_TA_ACK state");
        assert (DUT.cphy_tx_fsm_U0.RxUlpsEsc    === DUT.RxUlpsEsc   ) else $error("RxUlpsEsc    not asserted in TX_TA_ACK state");
        assert (DUT.cphy_tx_fsm_U0.RxLpdtEsc    === DUT.RxLpdtEsc   ) else $error("RxLpdtEsc    not asserted in TX_TA_ACK state");
		// LP Errors
        assert (DUT.cphy_tx_fsm_U0.ErrEsc     === DUT.ErrEsc    ) else $error("ErrEsc     not asserted in TX_TA_ACK state");   
        $display("[%0t] TX_TA_ACK values OK", $time);
    end
    endtask
	
    task assert_TX_STOP; 
    begin
        $display("[%0t] Checking TX_STOP values", $time);
        
        assert (DUT.cphy_tx_fsm_U0.Stopstate     === 1     ) else  $error("Stopstate     not 1      during TX_STOP");
        assert (DUT.cphy_tx_fsm_U0.Direction     === 0     ) else  $error("Direction     not 0      during TX_STOP");
        assert (DUT.cphy_tx_fsm_U0.LpTxEn        === 1     ) else  $error("LpTxEn        not 1      during TX_STOP");
        assert (DUT.cphy_tx_fsm_U0.TxCtrlOut     === 2'b00 ) else  $error("TXCtrlOut     not 2'b00  during TX_STOP");
        assert (DUT.cphy_tx_fsm_U0.RxTimerEn       === 0     ) else  $error("RxTimerEn       not 0      during TX_STOP");
        assert (DUT.cphy_tx_fsm_U0.RxTimerSeed     === 3'b000) else  $error("RxTimerSeed     not 3'b000 during TX_STOP");
		// LP PPI Signals
        assert (DUT.cphy_tx_fsm_U0.RxClkEsc     === DUT.RxClkEsc      ) else $error("RxClkEsc     not asserted in TX_STOP state");   
        assert (DUT.cphy_tx_fsm_U0.RxTriggerEsc === DUT.RxTriggerEsc) else $error("RxTriggerEsc not asserted in TX_STOP state");
        assert (DUT.cphy_tx_fsm_U0.RxUlpsEsc    === DUT.RxUlpsEsc   ) else $error("RxUlpsEsc    not asserted in TX_STOP state");
        assert (DUT.cphy_tx_fsm_U0.RxLpdtEsc    === DUT.RxLpdtEsc   ) else $error("RxLpdtEsc    not asserted in TX_STOP state");
		// LP Errors
        assert (DUT.cphy_tx_fsm_U0.ErrEsc     === DUT.ErrEsc    ) else $error("ErrEsc     not asserted in TX_STOP state");  
        $display("[%0t] TX_STOP values OK", $time);
    end
    endtask
	
    task assert_RX_ESC_RQST; 
    begin
        $display("[%0t] Checking RX_ESC_RQST values", $time);
        
        assert (DUT.cphy_tx_fsm_U0.Stopstate === 0) else  $error("Stopstate not 0 during RX_ESC_RQST");
		// LP PPI Signals
        assert (DUT.cphy_tx_fsm_U0.RxClkEsc     === DUT.RxClkEsc      ) else $error("RxClkEsc     not asserted in RX_ESC_RQST state");  
        assert (DUT.cphy_tx_fsm_U0.RxTriggerEsc === DUT.RxTriggerEsc) else $error("RxTriggerEsc not asserted in RX_ESC_RQST state");
        assert (DUT.cphy_tx_fsm_U0.RxUlpsEsc    === DUT.RxUlpsEsc   ) else $error("RxUlpsEsc    not asserted in RX_ESC_RQST state");
        assert (DUT.cphy_tx_fsm_U0.RxLpdtEsc    === DUT.RxLpdtEsc   ) else $error("RxLpdtEsc    not asserted in RX_ESC_RQST state");
		// LP Errors
        assert (DUT.cphy_tx_fsm_U0.ErrEsc     === DUT.ErrEsc    ) else $error("ErrEsc     not asserted in RX_ESC_RQST state");  
        $display("[%0t] RX_ESC_RQST values OK", $time);
    end
    endtask
	
    task assert_RX_ESC_CMD; 
    begin
        $display("[%0t] Checking RX_ESC_CMD values", $time);
        
        assert (DUT.cphy_tx_fsm_U0.Stopstate    === 0) else  $error("Stopstate    not 0 during RX_ESC_CMD");
        assert (DUT.cphy_tx_fsm_U0.EscDecoderEn === 1) else  $error("EscDecoderEn not 1 during RX_ESC_CMD");
		// LP PPI Signals
        assert (DUT.cphy_tx_fsm_U0.RxClkEsc     === DUT.RxClkEsc      ) else $error("RxClkEsc     not asserted in RX_ESC_CMD state"); 
        assert (DUT.cphy_tx_fsm_U0.RxTriggerEsc === DUT.RxTriggerEsc) else $error("RxTriggerEsc not asserted in RX_ESC_CMD state");
        assert (DUT.cphy_tx_fsm_U0.RxUlpsEsc    === DUT.RxUlpsEsc   ) else $error("RxUlpsEsc    not asserted in RX_ESC_CMD state");
        assert (DUT.cphy_tx_fsm_U0.RxLpdtEsc    === DUT.RxLpdtEsc   ) else $error("RxLpdtEsc    not asserted in RX_ESC_CMD state");
		// LP Errors
        assert (DUT.cphy_tx_fsm_U0.ErrEsc     === DUT.ErrEsc    ) else $error("ErrEsc     not asserted in RX_ESC_CMD state");   
        $display("[%0t] RX_ESC_CMD values OK", $time);
    end
    endtask
	
    task assert_RX_WAIT; 
    begin
        $display("[%0t] Checking RX_WAIT values", $time);
        
        assert (DUT.cphy_tx_fsm_U0.Stopstate     === 0) else  $error("Stopstate     not 0 during RX_WAIT");
        assert (DUT.cphy_tx_fsm_U0.CtrlDecoderEn === 1) else  $error("CtrlDecoderEn not 1 during RX_WAIT");
        assert (DUT.cphy_tx_fsm_U0.EscDecoderEn  === 0) else  $error("EscDecoderEn  not 0 during RX_WAIT");
		// LP PPI Signals
        assert (DUT.cphy_tx_fsm_U0.RxClkEsc     === DUT.RxClkEsc      ) else $error("RxClkEsc     not asserted in RX_WAIT state");   
        assert (DUT.cphy_tx_fsm_U0.RxTriggerEsc === DUT.RxTriggerEsc) else $error("RxTriggerEsc not asserted in RX_WAIT state");
        assert (DUT.cphy_tx_fsm_U0.RxUlpsEsc    === DUT.RxUlpsEsc   ) else $error("RxUlpsEsc    not asserted in RX_WAIT state");
        assert (DUT.cphy_tx_fsm_U0.RxLpdtEsc    === DUT.RxLpdtEsc   ) else $error("RxLpdtEsc    not asserted in RX_WAIT state");
		// LP Errors
        assert (DUT.cphy_tx_fsm_U0.ErrEsc     === DUT.ErrEsc    ) else $error("ErrEsc     not asserted in RX_WAIT state"); 
        $display("[%0t] RX_WAIT values OK", $time);
    end
    endtask
	
    task assert_RX_ULPS; 
    begin
        $display("[%0t] Checking RX_ULPS values", $time);
        
        assert (DUT.cphy_tx_fsm_U0.Stopstate      === 0) else  $error("Stopstate      not 0 during RX_ULPS");
        assert (DUT.cphy_tx_fsm_U0.UlpsActiveNot  === 0) else  $error("UlpsActiveNot  not 0 during RX_ULPS");
		// LP PPI Signals
        assert (DUT.cphy_tx_fsm_U0.RxClkEsc     === DUT.RxClkEsc      ) else $error("RxClkEsc     not asserted in RX_ULPS state"); 
        assert (DUT.cphy_tx_fsm_U0.RxTriggerEsc === DUT.RxTriggerEsc) else $error("RxTriggerEsc not asserted in RX_ULPS state");
        assert (DUT.cphy_tx_fsm_U0.RxUlpsEsc    === DUT.RxUlpsEsc   ) else $error("RxUlpsEsc    not asserted in RX_ULPS state");
        assert (DUT.cphy_tx_fsm_U0.RxLpdtEsc    === DUT.RxLpdtEsc   ) else $error("RxLpdtEsc    not asserted in RX_ULPS state");
		// LP Errors
        assert (DUT.cphy_tx_fsm_U0.ErrEsc     === DUT.ErrEsc    ) else $error("ErrEsc     not asserted in RX_ULPS state"); 
        $display("[%0t] RX_ULPS values OK", $time);
    end
    endtask
	
    task assert_RX_ULPS_T_WAKE_UP; 
    begin
        $display("[%0t] Checking RX_ULPS_T_WAKE_UP values", $time);
        
        assert (DUT.cphy_tx_fsm_U0.RxTimerEn        === 1     ) else  $error("RxTimerEn        not 0 during RX_ULPS_T_WAKE_UP");
        assert (DUT.cphy_tx_fsm_U0.UlpsActiveNot  === 1     ) else  $error("UlpsActiveNot  not 0 during RX_ULPS_T_WAKE_UP");
        assert (DUT.cphy_tx_fsm_U0.RxTimerSeed      === 3'b101) else  $error("RxTimerSeed      not 0 during RX_ULPS_T_WAKE_UP");
		// LP PPI Signals
        assert (DUT.cphy_tx_fsm_U0.RxClkEsc     === DUT.RxClkEsc      ) else $error("RxClkEsc     not asserted in RX_ULPS_T_WAKE_UP state"); 
        assert (DUT.cphy_tx_fsm_U0.RxTriggerEsc === DUT.RxTriggerEsc) else $error("RxTriggerEsc not asserted in RX_ULPS_T_WAKE_UP state");
        assert (DUT.cphy_tx_fsm_U0.RxUlpsEsc    === DUT.RxUlpsEsc   ) else $error("RxUlpsEsc    not asserted in RX_ULPS_T_WAKE_UP state");
        assert (DUT.cphy_tx_fsm_U0.RxLpdtEsc    === DUT.RxLpdtEsc   ) else $error("RxLpdtEsc    not asserted in RX_ULPS_T_WAKE_UP state");
		// LP Errors
        assert (DUT.cphy_tx_fsm_U0.ErrEsc     === DUT.ErrEsc    ) else $error("ErrEsc     not asserted in RX_ULPS_T_WAKE_UP state");
        $display("[%0t] RX_ULPS_T_WAKE_UP values OK", $time);
    end
    endtask
	
    task assert_RX_LPDT; 
    begin
        $display("[%0t] Checking RX_LPDT values", $time);
        
        assert (DUT.cphy_tx_fsm_U0.Stopstate     === 0) else  $error("Stopstate     not 0 during RX_LPDT");
        assert (DUT.cphy_tx_fsm_U0.CtrlDecoderEn === 0) else  $error("CtrlDecoderEn not 0 during RX_LPDT");  
		// LP PPI Signals
        assert (DUT.cphy_tx_fsm_U0.RxClkEsc     === DUT.RxClkEsc      ) else $error("RxClkEsc     not asserted in RX_LPDT state");  
        assert (DUT.cphy_tx_fsm_U0.RxTriggerEsc === DUT.RxTriggerEsc) else $error("RxTriggerEsc not asserted in RX_LPDT state");
        assert (DUT.cphy_tx_fsm_U0.RxUlpsEsc    === DUT.RxUlpsEsc   ) else $error("RxUlpsEsc    not asserted in RX_LPDT state");
        assert (DUT.cphy_tx_fsm_U0.RxLpdtEsc    === DUT.RxLpdtEsc   ) else $error("RxLpdtEsc    not asserted in RX_LPDT state");
		// LP Errors
        assert (DUT.cphy_tx_fsm_U0.ErrEsc     === DUT.ErrEsc    ) else $error("ErrEsc     not asserted in RX_LPDT state");  
        $display("[%0t] RX_LPDT values OK", $time);
    end
    endtask
	

reg [2:0] Sym;
always @(posedge TxSymbolClkHS) begin
  Sym <= DUT.HS_Encoder_U0.Sym;
end

endmodule