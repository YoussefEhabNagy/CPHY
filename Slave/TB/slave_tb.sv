`timescale 1ns / 1ps

module slave_tb;
    // Primary Inputs
    reg        A;
    reg        B;
    reg        C;
    reg        RstN;
    reg        RxClkFsm;
    reg        ForceRxmode;
    reg        TurnDisable;
    reg        TurnRequest;
    reg        ForceTxStopmode;
    reg        enable;
    reg        TxClkEsc;
    reg        TxReqEsc;
    reg        TxLpdtEsc;
    reg        TxUlpsEsc;
    reg        TxUlpsExit;
    reg [3:0]  TxTriggerEsc;
    reg        TxValidEsc;
    reg        CmdDone;
    reg        LpClk;
    // Outputs
    wire [15:0] RxDataHS;
    wire        RxValidHS;
    wire        RxActiveHS;
    wire        RxSyncHS;
    wire        RxInvalidCodeHS;
    wire        HsRxEn;
    wire [7:0]  RxEscData;
    wire        LpRxEn;
    wire        RxClkEscOut;
    wire        RxValidEsc;
    wire [3:0]  RxTriggerEsc;
    wire        RxUlpsEsc;
    wire        RxLpdtEsc;
    wire        LpTxEn;
    wire        LpCtrEscSel;
    wire [2:0]  EscSeqCtr;
    wire        EscSeqEn;
    wire        EscSerEn;
    wire        EscSerSeqSel;
    wire        EscEncoderEn;
    wire        DataValid;
    wire [1:0]  TxCtrlOut;
    wire        TxReadyEsc;
    wire        Direction;
    wire        Stopstate;
    wire        UlpsActiveNot;
    wire        ErrEsc;
    wire        ErrSyncEsc;
    wire        ErrControl;
    wire        ErrSotHS;
    wire        ErrSotSyncHS;

    // Instantiate DUT
    slave dut (
        //.RxClkEsc(LpClk),
        .A(A),
        .B(B),
        .C(C),
        .RxClkFsm(RxClkFsm),
        .RstN(RstN),
        .ForceRxmode(ForceRxmode),
        .TurnDisable(TurnDisable),
        .TurnRequest(TurnRequest),
        .ForceTxStopmode(ForceTxStopmode),
        .Enable(enable),
        .TxClkEsc(TxClkEsc),
        .TxReqEsc(TxReqEsc),
        .TxLpdtEsc(TxLpdtEsc),
        .TxUlpsEsc(TxUlpsEsc),
        .TxUlpsExit(TxUlpsExit),
        .TxTriggerEsc(TxTriggerEsc),
        .TxValidEsc(TxValidEsc),
        .CmdDone(CmdDone),
        .RxDataHS(RxDataHS),
        .RxValidHS(RxValidHS),
        .RxActiveHS(RxActiveHS),
        .RxSyncHS(RxSyncHS),
        .RxInvalidCodeHS(RxInvalidCodeHS),
        .HsRxEn(HsRxEn),
        .RxEscData(RxEscData),
        .LpRxEn(LpRxEn),
        .RxClkEscOut(RxClkEscOut),
        .RxValidEsc(RxValidEsc),
        .RxTriggerEsc(RxTriggerEsc),
        .RxUlpsEsc(RxUlpsEsc),
        .RxLpdtEsc(RxLpdtEsc),
        .LpTxEn(LpTxEn),
        .LpCtrEscSel(LpCtrEscSel),
        .EscSeqCtr(EscSeqCtr),
        .EscSeqEn(EscSeqEn),
        .EscSerEn(EscSerEn),
        .EscSerSeqSel(EscSerSeqSel),
        .EscEncoderEn(EscEncoderEn),
        .DataValid(DataValid),
        .TxCtrlOut(TxCtrlOut),
        .TxReadyEsc(TxReadyEsc),
        .Direction(Direction),
        .Stopstate(Stopstate),
        .UlpsActiveNot(UlpsActiveNot),
        .ErrEsc(ErrEsc),
        .ErrSyncEsc(ErrSyncEsc),
        .ErrControl(ErrControl),
        .ErrSotHS(ErrSotHS),
        .ErrSotSyncHS(ErrSotSyncHS)
    );

    // Main test sequence
    initial begin
        // Initialize
        initialize();
        // Reset sequence
        reset_dut();
        assert_reset_values();
        assert_Lp_state(dut.slave_fsm_inst.RX_STOP,"RX_STOP");
        
        //============================== HS Senario ===================
        // High-Speed Data Request
        Hs_Request();
        assert_Lp_state(dut.slave_fsm_inst.RX_HS_REQUEST,"RX_HS_REQUEST");
        //TERMEN_TIME 
        #50    
        //Receving Preamble
        Preamble();
        assert_Hs_state(dut.slave_fsm_inst.RX_HS_SYNC_SEARCH,"RX_HS_SYNC_SEARCH");
        //Receving SyncWord
        SyncWord();
        //#1
        assert_Hs_state(dut.slave_fsm_inst.RX_HS_RECEIVE_DATA,"RX_HS_RECEIVE_DATA");
        //Receving Data
        Data();
        assert_Hs_state(dut.slave_fsm_inst.RX_HS_RECEIVE_DATA,"RX_HS_RECEIVE_DATA");
        //Receving Post
        Post();
        #1
        assert_Hs_state(dut.slave_fsm_inst.RX_HS_POST,"RX_HS_POST");
        // Stop State
        #4
        assert_Lp_state(dut.slave_fsm_inst.RX_STOP,"RX_STOP");

        
        //============================== LP ESC Senario ===================
        //Receving LpRequest
        LpRequest(); // From RX_STOP to RX_LP_RQST to RX_LP_Yield 
        assert_Lp_state(dut.slave_fsm_inst.RX_LP_Yield,"RX_LP_Yield");
        //Receving EscapeEntry
        EscapeEntry(); // From RX_LP_Yield to RX_ESC_RQST to RX_Esc_Go
        assert_Lp_state(dut.slave_fsm_inst.RX_Esc_Go,"RX_Esc_Go");
        //Receving Command
        CommandSend();
        //Receving LpData
        LpData();
        assert_Lp_state(dut.slave_fsm_inst.RX_LPDT,"RX_LPDT");
        //Receving Spacs
        space();
        assert_Lp_state(dut.slave_fsm_inst.RX_LPDT,"RX_LPDT");
        //Receving LpData
        LpData();
        assert_Lp_state(dut.slave_fsm_inst.RX_LPDT,"RX_LPDT");
        //Receving EndEscape
        EndEscape();
        assert_RX_STOP();
        $display("\n[%0t] All tests completed", $time);
        $finish;
    end
    
    //Generatig FsmCLK
    always #1.667 RxClkFsm = ~RxClkFsm; // 1667 ps high, 1667 ps low => 3.334 ns period = ~300 MHz

    
    // Test tasks
    task initialize;
    begin
        A = 1;
        B = 1;
        C = 1;
        RxClkFsm = 0;
        RstN = 0;
        ForceRxmode = 0;
        TurnDisable = 0;
        TurnRequest = 0;
        ForceTxStopmode = 0;
        enable = 0;
        TxClkEsc = 0;
        TxReqEsc = 0;
        TxLpdtEsc = 0;
        TxUlpsEsc = 0;
        TxUlpsExit = 0;
        TxTriggerEsc = 0;
        TxValidEsc = 0;
        CmdDone = 0;
    end
    endtask
    
    
    task reset_dut;
    begin
        $display("[%0t] Applying reset", $time);
        RstN = 0;
        #100;
        RstN = 1;
        #50;
        $display("[%0t] Reset released", $time);
    end
    endtask
    
    task RX_STOP;
    begin 
        $display("[%0t] Applying RX_STOP", $time);
        A = 1; B = 1; C = 1;
        #(25);
        $display("[%0t] RX_STOP released", $time);
    end
    endtask  
      
    task Hs_Request;
    begin 
        $display("[%0t] Applying Hs_Request", $time);
        A = 0; B = 0; C = 1;
        #(25);
        A = 0; B = 0; C = 0;
        #(25);
        $display("[%0t] Hs_Request released", $time);
    end
    endtask
    
    task Preamble;
    begin
      $display("[%0t] Applying Preamble", $time);
       A = 1; B = 0;  C = 0;  // +x
       #2                           
       A = 1; B = 0;  C = 1;  // -y
       #2  
       A = 0; B = 0;  C = 1;  // +z
       #2
       A = 0; B = 1;  C = 1;  // -x
       #2
       A = 0; B = 1;  C = 0;  // +y
       #2
       A = 1; B = 1;  C = 0;  // -z
       #2
       A = 1; B = 0;  C = 0;  // +x
       #2
       A = 1; B = 0;  C = 1;  // -y
       #2  
       A = 0; B = 0;  C = 1;  // +z
       #2
       A = 0; B = 1;  C = 1;  // -x
       #2
       A = 0; B = 1;  C = 0;  // +y
       #2
       A = 1; B = 1;  C = 0;  // -z
       #2
       $display("[%0t] Preamble released", $time);
    end
    endtask

    task SyncWord;
    begin
       $display("[%0t] Applying SyncWord", $time);
       A = 1; B = 0;  C = 0;  // +x
       #2   
       A = 0; B = 1;  C = 1;  // -x
       #2   
       A = 1; B = 0;  C = 0;  // +x
       #2   
       A = 0; B = 1;  C = 1;  // -x
       #2   
       A = 1; B = 0;  C = 0;  // +x
       #2   
       A = 0; B = 1;  C = 1;  // -x
       #2   
       A = 0; B = 1;  C = 0;  // +y
       #2   
      $display("[%0t] SyncWord released", $time);
    end
    endtask

    task Data;
    begin
       $display("[%0t] Applying Data", $time);
       A = 0; B = 0;  C = 1;  // +z
       #2
       A = 0; B = 1;  C = 0;  // +y
       #2
       A = 1; B = 0;  C = 0;  // +x
       #2
       A = 0; B = 1;  C = 1;  // -x
       #2
       A = 1; B = 1;  C = 0;  // -z
       #2
       A = 0; B = 1;  C = 0;  // +y
       #2
      $display("[%0t] Data released", $time);
    end
    endtask

    task Post;
    begin
       $display("[%0t] Applying Post", $time);
       A = 1; B = 0;  C = 1;  // -y
       #2 
       A = 0; B = 1;  C = 0;  // +y
       #2
       A = 1; B = 0;  C = 1;  // -y
       #2
       A = 0; B = 1;  C = 0;  // +y
       #2
       A = 1; B = 0;  C = 1;  // -y
       #2
       A = 0; B = 1;  C = 0;  // +y
       #2
       A = 1; B = 0;  C = 1;  // -y
       #2
       $display("[%0t] Post released", $time);
    end
    endtask
    
   
    task LpRequest; 
    begin
        $display("[%0t] Applying LpRequest", $time);
        A = 1; B = 0; C = 0;
        #(25)
        A = 0; B = 0; C = 0;
        #(25)
        $display("[%0t] LpRequest released", $time);
    end
    endtask 
    
   
    task EscapeEntry; 
    begin
        $display("[%0t] Applying EscapeEntry", $time);
        A = 0; B = 0; C = 1;
        #(25)
        A = 0; B = 0; C = 0;
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
        A =  comma [i];
        C = ~comma [i];
        #(25);
        A = 0; B = 0; C = 0;
        #(25);
        end
        $display("[%0t] CommandSend released", $time);
    end
    endtask

    task LpData;
        begin
            $display("[%0t] Applying LpData", $time);
            A = 1; B = 0; C = 0; 
            #(25);
            A = 0; B = 0; C = 0;
            #(25);
            A = 0; B = 0; C = 1; 
            #(25);
            A = 0; B = 0; C = 0;
            #(25); 
            A = 1; B = 0; C = 0; 
            #(25);
            A = 0; B = 0; C = 0;
            #(25); 
            A = 1; B = 0; C = 0; 
            #(25);
            A = 0; B = 0; C = 0;
            #(25);
            A = 0; B = 0; C = 1; 
            #(25);
            A = 0; B = 0; C = 0;
            #(25);
            A = 1; B = 0; C = 0; 
            #(25);
            A = 0; B = 0; C = 0;
            #(25);
            A = 1; B = 0; C = 0; 
            #(25);
            A = 0; B = 0; C = 0; 
            #(25); 
            A = 1; B = 0; C = 0; 
            #(25);
            A = 0; B = 0; C = 0; 
            #(25);
            $display("[%0t] LpData released", $time);       
        end
        endtask
    
        task space;
        begin
        $display("[%0t] Applying space", $time);
        repeat(5)
        begin
           A = 0; B = 0; C = 0;
           #(25);
        end
        $display("[%0t] space released", $time);
        end
        endtask
    
        task EndEscape;
        begin
            $display("[%0t] Applying EndEscape", $time);  
            A = 1; B = 0; C = 0; 
            #(25);
            A = 1; B = 1; C = 1;
            #(25);
            $display("[%0t] EndEscape released", $time);
        end
        endtask

        task automatic assert_Lp_state(input [4:0] expected_state, input string message);
            if (dut.slave_fsm_inst.currentState !== expected_state) begin
                $error("[FAIL] State mismatch! Expected: %d, Got: %d  | %s",
                      expected_state ,
                      dut.slave_fsm_inst.currentState, message);
            end
            else begin
                $display("[PASS] State: %d - %s", expected_state , message);
                get_Lp_state_name(expected_state);
            end
        endtask
            
       
        task automatic assert_Hs_state(input [4:0] expected_state, input string message);
            if (dut.slave_fsm_inst.currentState !== expected_state) begin
                $error("[FAIL] State mismatch! Expected: %d, Got: %d  | %s",
                      expected_state ,
                      dut.slave_fsm_inst.currentState, message);
            end
            else begin
                $display("[PASS] State: %d - %s", expected_state , message);
                get_Hs_state_name(expected_state);
            end
        endtask
        
        task automatic get_Lp_state_name (input [4:0] state);
            case (state)
               dut.slave_fsm_inst.RX_STOP              :
               begin
                assert_RX_STOP();     
               end
               dut.slave_fsm_inst.RX_HS_REQUEST         : 
               begin
                assert_RX_HS_REQUEST();
               end
               dut.slave_fsm_inst.RX_LP_Yield           :
               begin
                assert_RX_LP_RQST();
               end
               dut.slave_fsm_inst.RX_TA_Wait           :
               begin
                assert_RX_TA_RQST();
               end
               dut.slave_fsm_inst.TX_TA_GET            :
               begin
                assert_TX_TA_GET();
               end
               dut.slave_fsm_inst.TX_TA_ACK            :
               begin
                assert_TX_TA_ACK();
               end
               dut.slave_fsm_inst.TX_STOP              :
               begin
                assert_TX_STOP();
               end
               dut.slave_fsm_inst.RX_Esc_Go            :
               begin
                assert_RX_ESC_RQST();
               end
               dut.slave_fsm_inst.RX_ESC_CMD           :
               begin
                assert_RX_ESC_CMD();
               end
               dut.slave_fsm_inst.RX_ULPS              :
               begin
               assert_RX_ULPS();
               end
               dut.slave_fsm_inst.RX_ULPS_T_WAKE_UP    :
               begin
                assert_RX_ULPS_T_WAKE_UP();
               end
               dut.slave_fsm_inst.RX_LPDT              :
               begin
                assert_RX_LPDT();
               end
               dut.slave_fsm_inst.RX_WAIT              :
               begin
                assert_RX_WAIT();
               end
            endcase 
        endtask
    
        task automatic get_Hs_state_name (input [4:0] state);
            case (state)
               dut.slave_fsm_inst.RX_HS_SYNC_SEARCH :
               begin
                assert_RX_HS_SYNC_SEARCH();     
               end
               dut.slave_fsm_inst.RX_HS_RECEIVE_DATA :
               begin
                assert_RX_HS_RECEIVE_DATA();
               end
               dut.slave_fsm_inst.RX_HS_POST         : 
               begin
               assert_RX_HS_POST();
               end
               
            endcase 
        endtask

    
    // Assertion tasks
    task assert_reset_values; // Like stop_state
    begin
        $display("[%0t] Checking reset values", $time);
        
        assert (dut.slave_fsm_inst.HsRxEn          === 0) else  $error("HsRxEn not 0 during reset");
        assert (dut.slave_fsm_inst.HsDecoderEn     === 0) else  $error("HsDecoderEn not 0 during reset");
        assert (dut.slave_fsm_inst.HSDeserEn       === 0) else  $error("HSDeserEn not 0 during reset");
        assert (dut.slave_fsm_inst.HsSeqDetectorEn === 0) else  $error("HsSeqDetectorEn not 0 during reset");
        assert (dut.slave_fsm_inst.RxValidHS       === 0) else  $error("RxValidHS not 0 during reset");
        assert (dut.slave_fsm_inst.RxActiveHS      === 0) else  $error("RxActiveHS not 0 during reset");
        assert (dut.slave_fsm_inst.LpRxEn          === 1) else  $error("LpRxEn not 1 during reset");
        assert (dut.slave_fsm_inst.EscDecoderEn    === 0) else  $error("EscDecoderEn not 0 during reset");
        assert (dut.slave_fsm_inst.EscDeserEn      === 0) else  $error("EscDeserEn not 0 during reset");
        assert (dut.slave_fsm_inst.CtrlDecoderEn   === 1) else  $error("CtrlDecoderEn not 1 during reset");
        assert (dut.slave_fsm_inst.Stopstate       === 1) else  $error("Stopstate not 1 during reset");
        assert (dut.slave_fsm_inst.Direction       === 1) else  $error("Direction not 1 during reset"); // Default to RX
        assert (dut.slave_fsm_inst.UlpsActiveNot   === 1) else  $error("UlpsActiveNot not 1 during reset"); // Default to RX
		// HS PPI Signals
        assert (dut.slave_fsm_inst.RxInvalidCodeHS === dut.InRxInvalidCodeHS)         else $error("RxInvalidCodeHS not asserted in reset state");        
        assert (dut.slave_fsm_inst.RxSyncHS        === (dut.DetectedSeq ==  4'b0010)) else $error("RxSyncHS        not asserted in reset state");  
		// HS Errors
        assert (dut.slave_fsm_inst.ErrSotHS     === dut.InErrSotHS)     else $error("ErrSotHS     not asserted in reset state");        
        assert (dut.slave_fsm_inst.ErrSotSyncHS === dut.InErrSotSyncHS) else $error("ErrSotSyncHS not asserted in reset state");
		// LP PPI Signals
        assert (dut.slave_fsm_inst.RxClkEsc     === dut.RxClkEsc      ) else $error("RxClkEsc     not asserted in reset state");        
        assert (dut.slave_fsm_inst.RxValidEsc   === dut.InRxValidEsc  ) else $error("RxValidEsc   not asserted in reset state");
        assert (dut.slave_fsm_inst.RxTriggerEsc === dut.InRxTriggerEsc) else $error("RxTriggerEsc not asserted in reset state");
        assert (dut.slave_fsm_inst.RxUlpsEsc    === dut.InRxUlpsEsc   ) else $error("RxUlpsEsc    not asserted in reset state");
        assert (dut.slave_fsm_inst.RxLpdtEsc    === dut.InRxLpdtEsc   ) else $error("RxLpdtEsc    not asserted in reset state");
		// LP Errors
        assert (dut.slave_fsm_inst.ErrEsc     === dut.InErrEsc    ) else $error("ErrEsc     not asserted in reset state");        
        assert (dut.slave_fsm_inst.ErrSyncEsc === dut.InErrSyncEsc) else $error("ErrSyncEsc not asserted in reset state");
        assert (dut.slave_fsm_inst.ErrControl === dut.InErrControl) else $error("ErrControl not asserted in reset state");
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
        
        assert (dut.slave_fsm_inst.HsRxEn          === 0) else  $error("HsRxEn          not 0 during RX_STOP");
        assert (dut.slave_fsm_inst.HsDecoderEn     === 0) else  $error("HsDecoderEn     not 0 during RX_STOP");
        assert (dut.slave_fsm_inst.HSDeserEn       === 0) else  $error("HSDeserEn       not 0 during RX_STOP");
        assert (dut.slave_fsm_inst.HsSeqDetectorEn === 0) else  $error("HsSeqDetectorEn not 0 during RX_STOP");
        assert (dut.slave_fsm_inst.RxValidHS       === 0) else  $error("RxValidHS       not 0 during RX_STOP");
        assert (dut.slave_fsm_inst.RxActiveHS      === 0) else  $error("RxActiveHS      not 0 during RX_STOP");
        assert (dut.slave_fsm_inst.LpRxEn          === 1) else  $error("LpRxEn          not 1 during RX_STOP");
        assert (dut.slave_fsm_inst.EscDecoderEn    === 0) else  $error("EscDecoderEn    not 0 during RX_STOP");
        assert (dut.slave_fsm_inst.EscDeserEn      === 0) else  $error("EscDeserEn      not 0 during RX_STOP");
        assert (dut.slave_fsm_inst.CtrlDecoderEn   === 1) else  $error("CtrlDecoderEn   not 1 during RX_STOP");
        assert (dut.slave_fsm_inst.Stopstate       === 1) else  $error("Stopstate       not 1 during RX_STOP");
        assert (dut.slave_fsm_inst.Direction       === 1) else  $error("Direction       not 1 during RX_STOP"); // Default to RX
        assert (dut.slave_fsm_inst.UlpsActiveNot   === 1) else  $error("UlpsActiveNot   not 1 during RX_STOP"); // Default to RX
		// HS PPI Signals
        assert (dut.slave_fsm_inst.RxInvalidCodeHS === dut.InRxInvalidCodeHS)         else $error("RxInvalidCodeHS not asserted in RX_STOP state");        
        assert (dut.slave_fsm_inst.RxSyncHS        === (dut.DetectedSeq ==  4'b0010)) else $error("RxSyncHS        not asserted in RX_STOP state");  
		// HS Errors
        assert (dut.slave_fsm_inst.ErrSotHS     === dut.InErrSotHS)     else $error("ErrSotHS     not asserted in RX_STOP state");        
        assert (dut.slave_fsm_inst.ErrSotSyncHS === dut.InErrSotSyncHS) else $error("ErrSotSyncHS not asserted in RX_STOP state");
		// LP PPI Signals
        assert (dut.slave_fsm_inst.RxClkEsc     === dut.RxClkEsc      ) else $error("RxClkEsc     not asserted in RX_STOP state");        
        assert (dut.slave_fsm_inst.RxValidEsc   === dut.InRxValidEsc  ) else $error("RxValidEsc   not asserted in RX_STOP state");
        assert (dut.slave_fsm_inst.RxTriggerEsc === dut.InRxTriggerEsc) else $error("RxTriggerEsc not asserted in RX_STOP state");
        assert (dut.slave_fsm_inst.RxUlpsEsc    === dut.InRxUlpsEsc   ) else $error("RxUlpsEsc    not asserted in RX_STOP state");
        assert (dut.slave_fsm_inst.RxLpdtEsc    === dut.InRxLpdtEsc   ) else $error("RxLpdtEsc    not asserted in RX_STOP state");
		// LP Errors
        assert (dut.slave_fsm_inst.ErrEsc     === dut.InErrEsc    ) else $error("ErrEsc     not asserted in RX_STOP state");        
        assert (dut.slave_fsm_inst.ErrSyncEsc === dut.InErrSyncEsc) else $error("ErrSyncEsc not asserted in RX_STOP state");
        assert (dut.slave_fsm_inst.ErrControl === dut.InErrControl) else $error("ErrControl not asserted in RX_STOP state");
        $display("[%0t] RX_STOP values OK", $time);
    end
    endtask
	
	
    task assert_RX_HS_REQUEST; 
    begin
        $display("[%0t] Checking RX_HS_REQUEST values", $time);
        
        assert (dut.slave_fsm_inst.Stopstate     === 0) else  $error("Stopstate     not 0 during RX_HS_REQUEST");
        assert (dut.slave_fsm_inst.RxActiveHS    === 1) else  $error("RxActiveHS    not 1 during RX_HS_REQUEST");
        assert (dut.slave_fsm_inst.HsRxEn        === 1) else  $error("HsRxEn        not 1 during RX_HS_REQUEST");
        assert (dut.slave_fsm_inst.LpRxEn        === 0) else  $error("LpRxEn        not 0 during RX_HS_REQUEST");
        assert (dut.slave_fsm_inst.CtrlDecoderEn === 0) else  $error("CtrlDecoderEn not 0 during RX_HS_REQUEST");
        assert (dut.slave_fsm_inst.HsDecoderEn   === 1) else  $error("HsDecoderEn   not 1 during RX_HS_REQUEST");
		// HS PPI Signals
        assert (dut.slave_fsm_inst.RxInvalidCodeHS === dut.InRxInvalidCodeHS)         else $error("RxInvalidCodeHS not asserted in RX_HS_REQUEST state");        
        assert (dut.slave_fsm_inst.RxSyncHS        === (dut.DetectedSeq ==  4'b0010)) else $error("RxSyncHS        not asserted in RX_HS_REQUEST state");  
		// HS Errors
        assert (dut.slave_fsm_inst.ErrSotHS     === dut.InErrSotHS)     else $error("ErrSotHS     not asserted in RX_HS_REQUEST state");        
        assert (dut.slave_fsm_inst.ErrSotSyncHS === dut.InErrSotSyncHS) else $error("ErrSotSyncHS not asserted in RX_HS_REQUEST state");
		// LP PPI Signals
        assert (dut.slave_fsm_inst.RxClkEsc     === dut.RxClkEsc      ) else $error("RxClkEsc     not asserted in RX_HS_REQUEST state");        
        assert (dut.slave_fsm_inst.RxValidEsc   === dut.InRxValidEsc  ) else $error("RxValidEsc   not asserted in RX_HS_REQUEST state");
        assert (dut.slave_fsm_inst.RxTriggerEsc === dut.InRxTriggerEsc) else $error("RxTriggerEsc not asserted in RX_HS_REQUEST state");
        assert (dut.slave_fsm_inst.RxUlpsEsc    === dut.InRxUlpsEsc   ) else $error("RxUlpsEsc    not asserted in RX_HS_REQUEST state");
        assert (dut.slave_fsm_inst.RxLpdtEsc    === dut.InRxLpdtEsc   ) else $error("RxLpdtEsc    not asserted in RX_HS_REQUEST state");
		// LP Errors
        assert (dut.slave_fsm_inst.ErrEsc     === dut.InErrEsc    ) else $error("ErrEsc     not asserted in RX_HS_REQUEST state");        
        assert (dut.slave_fsm_inst.ErrSyncEsc === dut.InErrSyncEsc) else $error("ErrSyncEsc not asserted in RX_HS_REQUEST state");
        assert (dut.slave_fsm_inst.ErrControl === dut.InErrControl) else $error("ErrControl not asserted in RX_HS_REQUEST state");
        $display("[%0t] RX_HS_REQUEST values OK", $time);
    end
    endtask
	
    task assert_RX_LP_RQST; 
    begin
        $display("[%0t] Checking RX_LP_RQST values", $time);
        
        assert (dut.slave_fsm_inst.Stopstate       === 0) else  $error("Stopstate not 0 during RX_LP_RQST");
		// HS PPI Signals
        assert (dut.slave_fsm_inst.RxInvalidCodeHS === dut.InRxInvalidCodeHS)         else $error("RxInvalidCodeHS not asserted in RX_LP_RQST state");        
        assert (dut.slave_fsm_inst.RxSyncHS        === (dut.DetectedSeq ==  4'b0010)) else $error("RxSyncHS        not asserted in RX_LP_RQST state");  
		// HS Errors
        assert (dut.slave_fsm_inst.ErrSotHS     === dut.InErrSotHS)     else $error("ErrSotHS     not asserted in RX_LP_RQST state");        
        assert (dut.slave_fsm_inst.ErrSotSyncHS === dut.InErrSotSyncHS) else $error("ErrSotSyncHS not asserted in RX_LP_RQST state");
		// LP PPI Signals
        assert (dut.slave_fsm_inst.RxClkEsc     === dut.RxClkEsc      ) else $error("RxClkEsc     not asserted in RX_LP_RQST state");        
        assert (dut.slave_fsm_inst.RxValidEsc   === dut.InRxValidEsc  ) else $error("RxValidEsc   not asserted in RX_LP_RQST state");
        assert (dut.slave_fsm_inst.RxTriggerEsc === dut.InRxTriggerEsc) else $error("RxTriggerEsc not asserted in RX_LP_RQST state");
        assert (dut.slave_fsm_inst.RxUlpsEsc    === dut.InRxUlpsEsc   ) else $error("RxUlpsEsc    not asserted in RX_LP_RQST state");
        assert (dut.slave_fsm_inst.RxLpdtEsc    === dut.InRxLpdtEsc   ) else $error("RxLpdtEsc    not asserted in RX_LP_RQST state");
		// LP Errors
        assert (dut.slave_fsm_inst.ErrEsc     === dut.InErrEsc    ) else $error("ErrEsc     not asserted in RX_LP_RQST state");        
        assert (dut.slave_fsm_inst.ErrSyncEsc === dut.InErrSyncEsc) else $error("ErrSyncEsc not asserted in RX_LP_RQST state");
        assert (dut.slave_fsm_inst.ErrControl === dut.InErrControl) else $error("ErrControl not asserted in RX_LP_RQST state");
        $display("[%0t] RX_LP_RQST values OK", $time);
    end
    endtask
	
    task assert_RX_TA_RQST; 
    begin
        $display("[%0t] Checking RX_TA_RQST values", $time);
		
        assert (dut.slave_fsm_inst.Stopstate === 0)      else  $error("Stopstate not 0 during RX_TA_RQST");
        assert (dut.slave_fsm_inst.TimerEn   === 1)      else  $error("TimerEn   not 1 during RX_TA_RQST");
        assert (dut.slave_fsm_inst.TimerSeed === 3'b011) else  $error("TimerSeed not 3'b011 during RX_TA_RQST");
		// HS PPI Signals
        assert (dut.slave_fsm_inst.RxInvalidCodeHS === dut.InRxInvalidCodeHS)         else $error("RxInvalidCodeHS not asserted in RX_TA_RQST state");        
        assert (dut.slave_fsm_inst.RxSyncHS        === (dut.DetectedSeq ==  4'b0010)) else $error("RxSyncHS        not asserted in RX_TA_RQST state");  
		// HS Errors
        assert (dut.slave_fsm_inst.ErrSotHS     === dut.InErrSotHS)     else $error("ErrSotHS     not asserted in RX_TA_RQST state");        
        assert (dut.slave_fsm_inst.ErrSotSyncHS === dut.InErrSotSyncHS) else $error("ErrSotSyncHS not asserted in RX_TA_RQST state");
		// LP PPI Signals
        assert (dut.slave_fsm_inst.RxClkEsc     === dut.RxClkEsc      ) else $error("RxClkEsc     not asserted in RX_TA_RQST state");        
        assert (dut.slave_fsm_inst.RxValidEsc   === dut.InRxValidEsc  ) else $error("RxValidEsc   not asserted in RX_TA_RQST state");
        assert (dut.slave_fsm_inst.RxTriggerEsc === dut.InRxTriggerEsc) else $error("RxTriggerEsc not asserted in RX_TA_RQST state");
        assert (dut.slave_fsm_inst.RxUlpsEsc    === dut.InRxUlpsEsc   ) else $error("RxUlpsEsc    not asserted in RX_TA_RQST state");
        assert (dut.slave_fsm_inst.RxLpdtEsc    === dut.InRxLpdtEsc   ) else $error("RxLpdtEsc    not asserted in RX_TA_RQST state");
		// LP Errors
        assert (dut.slave_fsm_inst.ErrEsc     === dut.InErrEsc    ) else $error("ErrEsc     not asserted in RX_TA_RQST state");        
        assert (dut.slave_fsm_inst.ErrSyncEsc === dut.InErrSyncEsc) else $error("ErrSyncEsc not asserted in RX_TA_RQST state");
        assert (dut.slave_fsm_inst.ErrControl === dut.InErrControl) else $error("ErrControl not asserted in RX_TA_RQST state");
        $display("[%0t] RX_TA_RQST values OK", $time);
    end
    endtask
	
    task assert_TX_TA_GET; 
    begin
        $display("[%0t] Checking TX_TA_GET values", $time);
        
        assert (dut.slave_fsm_inst.Stopstate     === 0     ) else  $error("Stopstate     not 0      during TX_TA_GET");
        assert (dut.slave_fsm_inst.Direction     === 0     ) else  $error("Direction     not 0      during TX_TA_GET");
        assert (dut.slave_fsm_inst.LpTxEn        === 1     ) else  $error("LpTxEn        not 1      during TX_TA_GET");
        assert (dut.slave_fsm_inst.CtrlDecoderEn === 1     ) else  $error("CtrlDecoderEn not 1      during TX_TA_GET");
        assert (dut.slave_fsm_inst.TxCtrlOut     === 2'b10 ) else  $error("TxCtrlOut     not 2'b10  during TX_TA_GET");
        assert (dut.slave_fsm_inst.TimerEn       === 1     ) else  $error("TimerEn       not 1      during TX_TA_GET");
        assert (dut.slave_fsm_inst.TimerSeed     === 3'b100) else  $error("TimerSeed     not 3'b100 during TX_TA_GET");
		// HS PPI Signals
        assert (dut.slave_fsm_inst.RxInvalidCodeHS === dut.InRxInvalidCodeHS)         else $error("RxInvalidCodeHS not asserted in TX_TA_GET state");        
        assert (dut.slave_fsm_inst.RxSyncHS        === (dut.DetectedSeq ==  4'b0010)) else $error("RxSyncHS        not asserted in TX_TA_GET state");  
		// HS Errors
        assert (dut.slave_fsm_inst.ErrSotHS     === dut.InErrSotHS)     else $error("ErrSotHS     not asserted in TX_TA_GET state");        
        assert (dut.slave_fsm_inst.ErrSotSyncHS === dut.InErrSotSyncHS) else $error("ErrSotSyncHS not asserted in TX_TA_GET state");
		// LP PPI Signals
        assert (dut.slave_fsm_inst.RxClkEsc     === dut.RxClkEsc      ) else $error("RxClkEsc     not asserted in TX_TA_GET state");        
        assert (dut.slave_fsm_inst.RxValidEsc   === dut.InRxValidEsc  ) else $error("RxValidEsc   not asserted in TX_TA_GET state");
        assert (dut.slave_fsm_inst.RxTriggerEsc === dut.InRxTriggerEsc) else $error("RxTriggerEsc not asserted in TX_TA_GET state");
        assert (dut.slave_fsm_inst.RxUlpsEsc    === dut.InRxUlpsEsc   ) else $error("RxUlpsEsc    not asserted in TX_TA_GET state");
        assert (dut.slave_fsm_inst.RxLpdtEsc    === dut.InRxLpdtEsc   ) else $error("RxLpdtEsc    not asserted in TX_TA_GET state");
		// LP Errors
        assert (dut.slave_fsm_inst.ErrEsc     === dut.InErrEsc    ) else $error("ErrEsc     not asserted in TX_TA_GET state");        
        assert (dut.slave_fsm_inst.ErrSyncEsc === dut.InErrSyncEsc) else $error("ErrSyncEsc not asserted in TX_TA_GET state");
        assert (dut.slave_fsm_inst.ErrControl === dut.InErrControl) else $error("ErrControl not asserted in TX_TA_GET state");
        $display("[%0t] TX_TA_GET values OK", $time);
    end
    endtask
	
    task assert_TX_TA_ACK; 
    begin
        $display("[%0t] Checking TX_TA_ACK values", $time);
        
        assert (dut.slave_fsm_inst.Stopstate     === 0     ) else  $error("Stopstate     not 0      during TX_TA_ACK");
        assert (dut.slave_fsm_inst.Direction     === 0     ) else  $error("Direction     not 0      during TX_TA_ACK");
        assert (dut.slave_fsm_inst.LpTxEn        === 1     ) else  $error("LpTxEn        not 1      during TX_TA_ACK");
        assert (dut.slave_fsm_inst.CtrlDecoderEn === 1     ) else  $error("CtrlDecoderEn not 1      during TX_TA_ACK");
        assert (dut.slave_fsm_inst.TxCtrlOut     === 2'b01 ) else  $error("TxCtrlOut     not 2'b01  during TX_TA_ACK");
        assert (dut.slave_fsm_inst.TimerEn       === 1     ) else  $error("TimerEn       not 1      during TX_TA_ACK");
        assert (dut.slave_fsm_inst.TimerSeed     === 3'b000) else  $error("TimerSeed     not 3'b000 during TX_TA_ACK");
		// HS PPI Signals
        assert (dut.slave_fsm_inst.RxInvalidCodeHS === dut.InRxInvalidCodeHS)         else $error("RxInvalidCodeHS not asserted in TX_TA_ACK state");        
        assert (dut.slave_fsm_inst.RxSyncHS        === (dut.DetectedSeq ==  4'b0010)) else $error("RxSyncHS        not asserted in TX_TA_ACK state");  
		// HS Errors
        assert (dut.slave_fsm_inst.ErrSotHS     === dut.InErrSotHS)     else $error("ErrSotHS     not asserted in TX_TA_ACK state");        
        assert (dut.slave_fsm_inst.ErrSotSyncHS === dut.InErrSotSyncHS) else $error("ErrSotSyncHS not asserted in TX_TA_ACK state");
		// LP PPI Signals
        assert (dut.slave_fsm_inst.RxClkEsc     === dut.RxClkEsc      ) else $error("RxClkEsc     not asserted in TX_TA_ACK state");        
        assert (dut.slave_fsm_inst.RxValidEsc   === dut.InRxValidEsc  ) else $error("RxValidEsc   not asserted in TX_TA_ACK state");
        assert (dut.slave_fsm_inst.RxTriggerEsc === dut.InRxTriggerEsc) else $error("RxTriggerEsc not asserted in TX_TA_ACK state");
        assert (dut.slave_fsm_inst.RxUlpsEsc    === dut.InRxUlpsEsc   ) else $error("RxUlpsEsc    not asserted in TX_TA_ACK state");
        assert (dut.slave_fsm_inst.RxLpdtEsc    === dut.InRxLpdtEsc   ) else $error("RxLpdtEsc    not asserted in TX_TA_ACK state");
		// LP Errors
        assert (dut.slave_fsm_inst.ErrEsc     === dut.InErrEsc    ) else $error("ErrEsc     not asserted in TX_TA_ACK state");        
        assert (dut.slave_fsm_inst.ErrSyncEsc === dut.InErrSyncEsc) else $error("ErrSyncEsc not asserted in TX_TA_ACK state");
        assert (dut.slave_fsm_inst.ErrControl === dut.InErrControl) else $error("ErrControl not asserted in TX_TA_ACK state");
        $display("[%0t] TX_TA_ACK values OK", $time);
    end
    endtask
	
    task assert_TX_STOP; 
    begin
        $display("[%0t] Checking TX_STOP values", $time);
        
        assert (dut.slave_fsm_inst.Stopstate     === 1     ) else  $error("Stopstate     not 1      during TX_STOP");
        assert (dut.slave_fsm_inst.Direction     === 0     ) else  $error("Direction     not 0      during TX_STOP");
        assert (dut.slave_fsm_inst.LpTxEn        === 1     ) else  $error("LpTxEn        not 1      during TX_STOP");
        assert (dut.slave_fsm_inst.CtrlDecoderEn === 1     ) else  $error("CtrlDecoderEn not 1      during TX_STOP");
        assert (dut.slave_fsm_inst.TxCtrlOut     === 2'b00 ) else  $error("TxCtrlOut     not 2'b00  during TX_STOP");
        assert (dut.slave_fsm_inst.TimerEn       === 0     ) else  $error("TimerEn       not 0      during TX_STOP");
        assert (dut.slave_fsm_inst.TimerSeed     === 3'b000) else  $error("TimerSeed     not 3'b000 during TX_STOP");
		// HS PPI Signals
        assert (dut.slave_fsm_inst.RxInvalidCodeHS === dut.InRxInvalidCodeHS)         else $error("RxInvalidCodeHS not asserted in TX_STOP state");        
        assert (dut.slave_fsm_inst.RxSyncHS        === (dut.DetectedSeq ==  4'b0010)) else $error("RxSyncHS        not asserted in TX_STOP state");  
		// HS Errors
        assert (dut.slave_fsm_inst.ErrSotHS     === dut.InErrSotHS)     else $error("ErrSotHS     not asserted in TX_STOP state");        
        assert (dut.slave_fsm_inst.ErrSotSyncHS === dut.InErrSotSyncHS) else $error("ErrSotSyncHS not asserted in TX_STOP state");
		// LP PPI Signals
        assert (dut.slave_fsm_inst.RxClkEsc     === dut.RxClkEsc      ) else $error("RxClkEsc     not asserted in TX_STOP state");        
        assert (dut.slave_fsm_inst.RxValidEsc   === dut.InRxValidEsc  ) else $error("RxValidEsc   not asserted in TX_STOP state");
        assert (dut.slave_fsm_inst.RxTriggerEsc === dut.InRxTriggerEsc) else $error("RxTriggerEsc not asserted in TX_STOP state");
        assert (dut.slave_fsm_inst.RxUlpsEsc    === dut.InRxUlpsEsc   ) else $error("RxUlpsEsc    not asserted in TX_STOP state");
        assert (dut.slave_fsm_inst.RxLpdtEsc    === dut.InRxLpdtEsc   ) else $error("RxLpdtEsc    not asserted in TX_STOP state");
		// LP Errors
        assert (dut.slave_fsm_inst.ErrEsc     === dut.InErrEsc    ) else $error("ErrEsc     not asserted in TX_STOP state");        
        assert (dut.slave_fsm_inst.ErrSyncEsc === dut.InErrSyncEsc) else $error("ErrSyncEsc not asserted in TX_STOP state");
        assert (dut.slave_fsm_inst.ErrControl === dut.InErrControl) else $error("ErrControl not asserted in TX_STOP state");
        $display("[%0t] TX_STOP values OK", $time);
    end
    endtask
	
    task assert_RX_ESC_RQST; 
    begin
        $display("[%0t] Checking RX_ESC_RQST values", $time);
        
        assert (dut.slave_fsm_inst.Stopstate === 0) else  $error("Stopstate not 0 during RX_ESC_RQST");
		// HS PPI Signals
        assert (dut.slave_fsm_inst.RxInvalidCodeHS === dut.InRxInvalidCodeHS)         else $error("RxInvalidCodeHS not asserted in RX_ESC_RQST state");        
        assert (dut.slave_fsm_inst.RxSyncHS        === (dut.DetectedSeq ==  4'b0010)) else $error("RxSyncHS        not asserted in RX_ESC_RQST state");  
		// HS Errors
        assert (dut.slave_fsm_inst.ErrSotHS     === dut.InErrSotHS)     else $error("ErrSotHS     not asserted in RX_ESC_RQST state");        
        assert (dut.slave_fsm_inst.ErrSotSyncHS === dut.InErrSotSyncHS) else $error("ErrSotSyncHS not asserted in RX_ESC_RQST state");
		// LP PPI Signals
        assert (dut.slave_fsm_inst.RxClkEsc     === dut.RxClkEsc      ) else $error("RxClkEsc     not asserted in RX_ESC_RQST state");        
        assert (dut.slave_fsm_inst.RxValidEsc   === dut.InRxValidEsc  ) else $error("RxValidEsc   not asserted in RX_ESC_RQST state");
        assert (dut.slave_fsm_inst.RxTriggerEsc === dut.InRxTriggerEsc) else $error("RxTriggerEsc not asserted in RX_ESC_RQST state");
        assert (dut.slave_fsm_inst.RxUlpsEsc    === dut.InRxUlpsEsc   ) else $error("RxUlpsEsc    not asserted in RX_ESC_RQST state");
        assert (dut.slave_fsm_inst.RxLpdtEsc    === dut.InRxLpdtEsc   ) else $error("RxLpdtEsc    not asserted in RX_ESC_RQST state");
		// LP Errors
        assert (dut.slave_fsm_inst.ErrEsc     === dut.InErrEsc    ) else $error("ErrEsc     not asserted in RX_ESC_RQST state");        
        assert (dut.slave_fsm_inst.ErrSyncEsc === dut.InErrSyncEsc) else $error("ErrSyncEsc not asserted in RX_ESC_RQST state");
        assert (dut.slave_fsm_inst.ErrControl === dut.InErrControl) else $error("ErrControl not asserted in RX_ESC_RQST state");
        $display("[%0t] RX_ESC_RQST values OK", $time);
    end
    endtask
	
    task assert_RX_ESC_CMD; 
    begin
        $display("[%0t] Checking RX_ESC_CMD values", $time);
        
        assert (dut.slave_fsm_inst.Stopstate    === 0) else  $error("Stopstate    not 0 during RX_ESC_CMD");
        assert (dut.slave_fsm_inst.EscDecoderEn === 1) else  $error("EscDecoderEn not 1 during RX_ESC_CMD");
		// HS PPI Signals
        assert (dut.slave_fsm_inst.RxInvalidCodeHS === dut.InRxInvalidCodeHS)         else $error("RxInvalidCodeHS not asserted in RX_ESC_CMD state");        
        assert (dut.slave_fsm_inst.RxSyncHS        === (dut.DetectedSeq ==  4'b0010)) else $error("RxSyncHS        not asserted in RX_ESC_CMD state");  
		// HS Errors
        assert (dut.slave_fsm_inst.ErrSotHS     === dut.InErrSotHS)     else $error("ErrSotHS     not asserted in RX_ESC_CMD state");        
        assert (dut.slave_fsm_inst.ErrSotSyncHS === dut.InErrSotSyncHS) else $error("ErrSotSyncHS not asserted in RX_ESC_CMD state");
		// LP PPI Signals
        assert (dut.slave_fsm_inst.RxClkEsc     === dut.RxClkEsc      ) else $error("RxClkEsc     not asserted in RX_ESC_CMD state");        
        assert (dut.slave_fsm_inst.RxValidEsc   === dut.InRxValidEsc  ) else $error("RxValidEsc   not asserted in RX_ESC_CMD state");
        assert (dut.slave_fsm_inst.RxTriggerEsc === dut.InRxTriggerEsc) else $error("RxTriggerEsc not asserted in RX_ESC_CMD state");
        assert (dut.slave_fsm_inst.RxUlpsEsc    === dut.InRxUlpsEsc   ) else $error("RxUlpsEsc    not asserted in RX_ESC_CMD state");
        assert (dut.slave_fsm_inst.RxLpdtEsc    === dut.InRxLpdtEsc   ) else $error("RxLpdtEsc    not asserted in RX_ESC_CMD state");
		// LP Errors
        assert (dut.slave_fsm_inst.ErrEsc     === dut.InErrEsc    ) else $error("ErrEsc     not asserted in RX_ESC_CMD state");        
        assert (dut.slave_fsm_inst.ErrSyncEsc === dut.InErrSyncEsc) else $error("ErrSyncEsc not asserted in RX_ESC_CMD state");
        assert (dut.slave_fsm_inst.ErrControl === dut.InErrControl) else $error("ErrControl not asserted in RX_ESC_CMD state");
        $display("[%0t] RX_ESC_CMD values OK", $time);
    end
    endtask
	
    task assert_RX_WAIT; 
    begin
        $display("[%0t] Checking RX_WAIT values", $time);
        
        assert (dut.slave_fsm_inst.Stopstate     === 0) else  $error("Stopstate     not 0 during RX_WAIT");
        assert (dut.slave_fsm_inst.CtrlDecoderEn === 1) else  $error("CtrlDecoderEn not 1 during RX_WAIT");
        assert (dut.slave_fsm_inst.EscDecoderEn  === 0) else  $error("EscDecoderEn  not 0 during RX_WAIT");
		// HS PPI Signals
        assert (dut.slave_fsm_inst.RxInvalidCodeHS === dut.InRxInvalidCodeHS)         else $error("RxInvalidCodeHS not asserted in RX_WAIT state");        
        assert (dut.slave_fsm_inst.RxSyncHS        === (dut.DetectedSeq ==  4'b0010)) else $error("RxSyncHS        not asserted in RX_WAIT state");  
		// HS Errors
        assert (dut.slave_fsm_inst.ErrSotHS     === dut.InErrSotHS)     else $error("ErrSotHS     not asserted in RX_WAIT state");        
        assert (dut.slave_fsm_inst.ErrSotSyncHS === dut.InErrSotSyncHS) else $error("ErrSotSyncHS not asserted in RX_WAIT state");
		// LP PPI Signals
        assert (dut.slave_fsm_inst.RxClkEsc     === dut.RxClkEsc      ) else $error("RxClkEsc     not asserted in RX_WAIT state");        
        assert (dut.slave_fsm_inst.RxValidEsc   === dut.InRxValidEsc  ) else $error("RxValidEsc   not asserted in RX_WAIT state");
        assert (dut.slave_fsm_inst.RxTriggerEsc === dut.InRxTriggerEsc) else $error("RxTriggerEsc not asserted in RX_WAIT state");
        assert (dut.slave_fsm_inst.RxUlpsEsc    === dut.InRxUlpsEsc   ) else $error("RxUlpsEsc    not asserted in RX_WAIT state");
        assert (dut.slave_fsm_inst.RxLpdtEsc    === dut.InRxLpdtEsc   ) else $error("RxLpdtEsc    not asserted in RX_WAIT state");
		// LP Errors
        assert (dut.slave_fsm_inst.ErrEsc     === dut.InErrEsc    ) else $error("ErrEsc     not asserted in RX_WAIT state");        
        assert (dut.slave_fsm_inst.ErrSyncEsc === dut.InErrSyncEsc) else $error("ErrSyncEsc not asserted in RX_WAIT state");
        assert (dut.slave_fsm_inst.ErrControl === dut.InErrControl) else $error("ErrControl not asserted in RX_WAIT state");
        $display("[%0t] RX_WAIT values OK", $time);
    end
    endtask
	
    task assert_RX_ULPS; 
    begin
        $display("[%0t] Checking RX_ULPS values", $time);
        
        assert (dut.slave_fsm_inst.Stopstate      === 0) else  $error("Stopstate      not 0 during RX_ULPS");
        assert (dut.slave_fsm_inst.UlpsActiveNot  === 0) else  $error("UlpsActiveNot  not 0 during RX_ULPS");
		// HS PPI Signals
        assert (dut.slave_fsm_inst.RxInvalidCodeHS === dut.InRxInvalidCodeHS)         else $error("RxInvalidCodeHS not asserted in RX_ULPS state");        
        assert (dut.slave_fsm_inst.RxSyncHS        === (dut.DetectedSeq ==  4'b0010)) else $error("RxSyncHS        not asserted in RX_ULPS state");  
		// HS Errors
        assert (dut.slave_fsm_inst.ErrSotHS     === dut.InErrSotHS)     else $error("ErrSotHS     not asserted in RX_ULPS state");        
        assert (dut.slave_fsm_inst.ErrSotSyncHS === dut.InErrSotSyncHS) else $error("ErrSotSyncHS not asserted in RX_ULPS state");
		// LP PPI Signals
        assert (dut.slave_fsm_inst.RxClkEsc     === dut.RxClkEsc      ) else $error("RxClkEsc     not asserted in RX_ULPS state");        
        assert (dut.slave_fsm_inst.RxValidEsc   === dut.InRxValidEsc  ) else $error("RxValidEsc   not asserted in RX_ULPS state");
        assert (dut.slave_fsm_inst.RxTriggerEsc === dut.InRxTriggerEsc) else $error("RxTriggerEsc not asserted in RX_ULPS state");
        assert (dut.slave_fsm_inst.RxUlpsEsc    === dut.InRxUlpsEsc   ) else $error("RxUlpsEsc    not asserted in RX_ULPS state");
        assert (dut.slave_fsm_inst.RxLpdtEsc    === dut.InRxLpdtEsc   ) else $error("RxLpdtEsc    not asserted in RX_ULPS state");
		// LP Errors
        assert (dut.slave_fsm_inst.ErrEsc     === dut.InErrEsc    ) else $error("ErrEsc     not asserted in RX_ULPS state");        
        assert (dut.slave_fsm_inst.ErrSyncEsc === dut.InErrSyncEsc) else $error("ErrSyncEsc not asserted in RX_ULPS state");
        assert (dut.slave_fsm_inst.ErrControl === dut.InErrControl) else $error("ErrControl not asserted in RX_ULPS state");
        $display("[%0t] RX_ULPS values OK", $time);
    end
    endtask
	
    task assert_RX_ULPS_T_WAKE_UP; 
    begin
        $display("[%0t] Checking RX_ULPS_T_WAKE_UP values", $time);
        
        assert (dut.slave_fsm_inst.TimerEn        === 1     ) else  $error("TimerEn        not 0 during RX_ULPS_T_WAKE_UP");
        assert (dut.slave_fsm_inst.UlpsActiveNot  === 1     ) else  $error("UlpsActiveNot  not 0 during RX_ULPS_T_WAKE_UP");
        assert (dut.slave_fsm_inst.TimerSeed      === 3'b101) else  $error("TimerSeed      not 0 during RX_ULPS_T_WAKE_UP");
		// HS PPI Signals
        assert (dut.slave_fsm_inst.RxInvalidCodeHS === dut.InRxInvalidCodeHS)         else $error("RxInvalidCodeHS not asserted in RX_ULPS_T_WAKE_UP state");        
        assert (dut.slave_fsm_inst.RxSyncHS        === (dut.DetectedSeq ==  4'b0010)) else $error("RxSyncHS        not asserted in RX_ULPS_T_WAKE_UP state");  
		// HS Errors
        assert (dut.slave_fsm_inst.ErrSotHS     === dut.InErrSotHS)     else $error("ErrSotHS     not asserted in RX_ULPS_T_WAKE_UP state");        
        assert (dut.slave_fsm_inst.ErrSotSyncHS === dut.InErrSotSyncHS) else $error("ErrSotSyncHS not asserted in RX_ULPS_T_WAKE_UP state");
		// LP PPI Signals
        assert (dut.slave_fsm_inst.RxClkEsc     === dut.RxClkEsc      ) else $error("RxClkEsc     not asserted in RX_ULPS_T_WAKE_UP state");        
        assert (dut.slave_fsm_inst.RxValidEsc   === dut.InRxValidEsc  ) else $error("RxValidEsc   not asserted in RX_ULPS_T_WAKE_UP state");
        assert (dut.slave_fsm_inst.RxTriggerEsc === dut.InRxTriggerEsc) else $error("RxTriggerEsc not asserted in RX_ULPS_T_WAKE_UP state");
        assert (dut.slave_fsm_inst.RxUlpsEsc    === dut.InRxUlpsEsc   ) else $error("RxUlpsEsc    not asserted in RX_ULPS_T_WAKE_UP state");
        assert (dut.slave_fsm_inst.RxLpdtEsc    === dut.InRxLpdtEsc   ) else $error("RxLpdtEsc    not asserted in RX_ULPS_T_WAKE_UP state");
		// LP Errors
        assert (dut.slave_fsm_inst.ErrEsc     === dut.InErrEsc    ) else $error("ErrEsc     not asserted in RX_ULPS_T_WAKE_UP state");        
        assert (dut.slave_fsm_inst.ErrSyncEsc === dut.InErrSyncEsc) else $error("ErrSyncEsc not asserted in RX_ULPS_T_WAKE_UP state");
        assert (dut.slave_fsm_inst.ErrControl === dut.InErrControl) else $error("ErrControl not asserted in RX_ULPS_T_WAKE_UP state");
        $display("[%0t] RX_ULPS_T_WAKE_UP values OK", $time);
    end
    endtask
	
    task assert_RX_LPDT; 
    begin
        $display("[%0t] Checking RX_LPDT values", $time);
        
        assert (dut.slave_fsm_inst.Stopstate     === 0) else  $error("Stopstate     not 0 during RX_LPDT");
        assert (dut.slave_fsm_inst.CtrlDecoderEn === 0) else  $error("CtrlDecoderEn not 0 during RX_LPDT");
        assert (dut.slave_fsm_inst.EscDeserEn    === 1) else  $error("EscDeserEn    not 1 during RX_LPDT");
        assert (dut.slave_fsm_inst.EscDecoderEn  === 1) else  $error("EscDecoderEn  not 1 during RX_LPDT");     
		// HS PPI Signals
        assert (dut.slave_fsm_inst.RxInvalidCodeHS === dut.InRxInvalidCodeHS)         else $error("RxInvalidCodeHS not asserted in RX_LPDT state");        
        assert (dut.slave_fsm_inst.RxSyncHS        === (dut.DetectedSeq ==  4'b0010)) else $error("RxSyncHS        not asserted in RX_LPDT state");  
		// HS Errors
        assert (dut.slave_fsm_inst.ErrSotHS     === dut.InErrSotHS)     else $error("ErrSotHS     not asserted in RX_LPDT state");        
        assert (dut.slave_fsm_inst.ErrSotSyncHS === dut.InErrSotSyncHS) else $error("ErrSotSyncHS not asserted in RX_LPDT state");
		// LP PPI Signals
        assert (dut.slave_fsm_inst.RxClkEsc     === dut.RxClkEsc      ) else $error("RxClkEsc     not asserted in RX_LPDT state");        
        assert (dut.slave_fsm_inst.RxValidEsc   === dut.InRxValidEsc  ) else $error("RxValidEsc   not asserted in RX_LPDT state");
        assert (dut.slave_fsm_inst.RxTriggerEsc === dut.InRxTriggerEsc) else $error("RxTriggerEsc not asserted in RX_LPDT state");
        assert (dut.slave_fsm_inst.RxUlpsEsc    === dut.InRxUlpsEsc   ) else $error("RxUlpsEsc    not asserted in RX_LPDT state");
        assert (dut.slave_fsm_inst.RxLpdtEsc    === dut.InRxLpdtEsc   ) else $error("RxLpdtEsc    not asserted in RX_LPDT state");
		// LP Errors
        assert (dut.slave_fsm_inst.ErrEsc     === dut.InErrEsc    ) else $error("ErrEsc     not asserted in RX_LPDT state");        
        assert (dut.slave_fsm_inst.ErrSyncEsc === dut.InErrSyncEsc) else $error("ErrSyncEsc not asserted in RX_LPDT state");
        assert (dut.slave_fsm_inst.ErrControl === dut.InErrControl) else $error("ErrControl not asserted in RX_LPDT state");
        $display("[%0t] RX_LPDT values OK", $time);
    end
    endtask
	
	//===================================================================================================
	//========================================= HS FSM Assertion Tasks ==================================
	//===================================================================================================
    task assert_RX_HS_SYNC_SEARCH;
    begin
		$display("[%0t] Checking RX_HS_SYNC_SEARCH values", $time);
        assert (dut.slave_fsm_inst.Stopstate       === 0) else $error("Stopstate       not 0 in RX_HS_SYNC_SEARCH state");
        assert (dut.slave_fsm_inst.RxActiveHS      === 1) else $error("RxActiveHS      not 1 in RX_HS_SYNC_SEARCH state");
        assert (dut.slave_fsm_inst.HsRxEn          === 1) else $error("HsRxEn          not 1 in RX_HS_SYNC_SEARCH state");        
        assert (dut.slave_fsm_inst.CtrlDecoderEn   === 0) else $error("CtrlDecoderEn   not 0 in RX_HS_SYNC_SEARCH state");        
        assert (dut.slave_fsm_inst.HsDecoderEn     === 1) else $error("HsDecoderEn     not 1 in RX_HS_SYNC_SEARCH state");        
        assert (dut.slave_fsm_inst.HsSeqDetectorEn === 1) else $error("HsSeqDetectorEn not 1 in RX_HS_SYNC_SEARCH state");        
		// HS PPI Signals
        assert (dut.slave_fsm_inst.RxInvalidCodeHS === dut.InRxInvalidCodeHS)         else $error("RxInvalidCodeHS not asserted in RX_HS_SYNC_SEARCH state");        
        assert (dut.slave_fsm_inst.RxSyncHS        === (dut.DetectedSeq ==  4'b0010)) else $error("RxSyncHS        not asserted in RX_HS_SYNC_SEARCH state");  
		// HS Errors
        assert (dut.slave_fsm_inst.ErrSotHS     === dut.InErrSotHS)     else $error("ErrSotHS     not asserted in RX_HS_SYNC_SEARCH state");        
        assert (dut.slave_fsm_inst.ErrSotSyncHS === dut.InErrSotSyncHS) else $error("ErrSotSyncHS not asserted in RX_HS_SYNC_SEARCH state");
		$display("[%0t] RX_HS_SYNC_SEARCH values OK", $time);        
    end
    endtask


    task assert_RX_HS_RECEIVE_DATA;
    begin
		$display("[%0t] Checking RX_HS_RECEIVE_DATA values", $time);
        assert (dut.slave_fsm_inst.Stopstate       === 0) else $error("Stopstate       not 0 in RX_HS_RECEIVE_DATA state");
        assert (dut.slave_fsm_inst.RxValidHS       === 1) else $error("RxValidHS       not 1 in RX_HS_RECEIVE_DATA state");
        assert (dut.slave_fsm_inst.RxActiveHS      === 1) else $error("RxActiveHS      not 1 in RX_HS_RECEIVE_DATA state");        
        assert (dut.slave_fsm_inst.HsRxEn          === 1) else $error("HsRxEn          not 1 in RX_HS_RECEIVE_DATA state");        
        assert (dut.slave_fsm_inst.CtrlDecoderEn   === 0) else $error("CtrlDecoderEn   not 0 in RX_HS_RECEIVE_DATA state");        
        assert (dut.slave_fsm_inst.HsDecoderEn     === 1) else $error("HsDecoderEn     not 1 in RX_HS_RECEIVE_DATA state");        
        assert (dut.slave_fsm_inst.HSDeserEn       === 1) else $error("HSDeserEn       not 1 in RX_HS_RECEIVE_DATA state");        
        assert (dut.slave_fsm_inst.HsSeqDetectorEn === 1) else $error("HsSeqDetectorEn not 1 in RX_HS_RECEIVE_DATA state");        
		// HS PPI Signals
        assert (dut.slave_fsm_inst.RxInvalidCodeHS === dut.InRxInvalidCodeHS)         else $error("RxInvalidCodeHS not asserted in RX_HS_RECEIVE_DATA state");        
        assert (dut.slave_fsm_inst.RxSyncHS        === (dut.DetectedSeq ==  4'b0010)) else $error("RxSyncHS        not asserted in RX_HS_RECEIVE_DATA state");  
		// HS Errors
        assert (dut.slave_fsm_inst.ErrSotHS     === dut.InErrSotHS)     else $error("ErrSotHS     not asserted in RX_HS_RECEIVE_DATA state");        
        assert (dut.slave_fsm_inst.ErrSotSyncHS === dut.InErrSotSyncHS) else $error("ErrSotSyncHS not asserted in RX_HS_RECEIVE_DATA state");
		$display("[%0t] RX_HS_RECEIVE_DATA values OK", $time);              
    end
    endtask


    task assert_RX_HS_POST;
    begin
		$display("[%0t] Checking RX_HS_POST values", $time);
        assert (dut.slave_fsm_inst.Stopstate       === 0) else $error("Stopstate       not 0 in RX_HS_POST state");
        assert (dut.slave_fsm_inst.RxValidHS       === 0) else $error("RxValidHS       not 0 in RX_HS_POST state");
        assert (dut.slave_fsm_inst.RxActiveHS      === 0) else $error("RxActiveHS      not 0 in RX_HS_POST state");        
        assert (dut.slave_fsm_inst.LpRxEn          === 1) else $error("LpRxEn          not 1 in RX_HS_POST state");        
        assert (dut.slave_fsm_inst.HsRxEn          === 0) else $error("HsRxEn          not 0 in RX_HS_POST state");        
        assert (dut.slave_fsm_inst.CtrlDecoderEn   === 1) else $error("CtrlDecoderEn   not 1 in RX_HS_POST state");        
        assert (dut.slave_fsm_inst.HsDecoderEn     === 0) else $error("HsDecoderEn     not 0 in RX_HS_POST state");        
        assert (dut.slave_fsm_inst.HSDeserEn       === 0) else $error("HSDeserEn       not 0 in RX_HS_POST state");        
        assert (dut.slave_fsm_inst.HsSeqDetectorEn === 0) else $error("HsSeqDetectorEn not 0 in RX_HS_POST state");             
		// HS PPI Signals
        assert (dut.slave_fsm_inst.RxInvalidCodeHS === dut.InRxInvalidCodeHS)         else $error("RxInvalidCodeHS not asserted in RX_HS_POST state");        
        assert (dut.slave_fsm_inst.RxSyncHS        === (dut.DetectedSeq ==  4'b0010)) else $error("RxSyncHS        not asserted in RX_HS_POST state");  
		// HS Errors
        assert (dut.slave_fsm_inst.ErrSotHS     === dut.InErrSotHS)     else $error("ErrSotHS     not asserted in RX_HS_POST state");        
        assert (dut.slave_fsm_inst.ErrSotSyncHS === dut.InErrSotSyncHS) else $error("ErrSotSyncHS not asserted in RX_HS_POST state"); 
		$display("[%0t] RX_HS_POST values OK", $time);          
    end
    endtask

endmodule