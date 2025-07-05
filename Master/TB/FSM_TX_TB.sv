`timescale 1ns/1ps

module cphy_tx_fsm_tb;

    // Parameters
    parameter Clk_Period = 10;

    //States
    localparam [4:0] 
    TX_STOP         = 5'd0,   
    TX_HS_REQUEST   = 5'd1,
    TX_LP_RQST      = 5'd2,
    TX_HS_PREPARE   = 5'd3,
    TX_LP_YIELD     = 5'd4,   
    TX_HS_PREAMBLE  = 5'd5,
    TX_TA_REQUEST   = 5'd6,
    TX_ESC_RQST     = 5'd7,  
    TX_HS_SYNC_WORD = 5'd8,
    TX_TA_GO        = 5'd9,
    TX_HS_SEND_DATA = 5'd10,
    TX_HS_POST      = 5'd11,
    RX_TA_LOOK      = 5'd12,
    RX_TA_ACK       = 5'd13,
    RX_STOP         = 5'd14,
    FORCE_RX        = 5'd15,
    TX_ESC_GO       = 5'd16, 
    TX_ESC_CMD      = 5'd17, 
    TX_LPDT         = 5'd18,  
    TX_TRIGGERS     = 5'd19,  
    TX_ULPS         = 5'd20,  
    TX_MARK         = 5'd21; 

    // Inputs
    reg clk;
    reg rst_n;
    reg TurnRequest;
    reg TxRequestEsc;
    reg TxRequestHS;
    reg TxUlpsEsc;
    reg TxLpdtEsc;
    reg TxUlpsExit;
    reg [3:0] TxTriggerEsc;
    reg Pre_Done;
    reg Sync_Done;
    reg Post_Done;
    reg Cmd_Done;
    reg TxSendSyncHS;
    reg [1:0] Ctrl_Decoder_Out;
    reg ForceRxmode;

    // Outputs
    wire Sequencer_En;
    wire Serializer_En;
    wire HSSerSeqSel;
    wire Encoder_En;
    wire TxReadyHS;
    wire TxReadyEsc;
    wire Direction;
    wire Stopstate;
    wire Esc_Sequencer_En;
    wire Esc_Serializer_En;
    wire EscSerSeqSel;
    wire Esc_Encoder_En;
    wire [3:0] Esc_Sequences;
    wire [1:0] TX_Ctrl_Out;
    wire LpCtrlEscSel;
    wire LpTxEn;
    wire HsTxEn;
    wire LpRxEn;
    wire Esc_Decoder_En;
    wire Ctrl_Decoder_En;
    wire Sync;
    wire Post;
    wire TxSendSynchS;
    wire TxSendSynchIS;

    cphy_tx_fsm DUT (
        .clk(clk),
        .rst_n(rst_n),
        .TurnRequest(TurnRequest),
        .TxRequestEsc(TxRequestEsc),
        .TxRequestHS(TxRequestHS),
        .TxUlpsEsc(TxUlpsEsc),
        .TxLpdtEsc(TxLpdtEsc),
        .TxUlpsExit(TxUlpsExit),
        .TxTriggerEsc(TxTriggerEsc),
        .Pre_Done(Pre_Done),
        .Sync_Done(Sync_Done),
        .Post_Done(Post_Done),
        .Cmd_Done(Cmd_Done),
        .TxSendSyncHS(TxSendSyncHS),
        .Ctrl_Decoder_Out(Ctrl_Decoder_Out),
        .ForceRxmode(ForceRxmode),
        .Sequencer_En(Sequencer_En),
        .Serializer_En(Serializer_En),
        .HSSerSeqSel(HSSerSeqSel),
        .Encoder_En(Encoder_En),
        .TxReadyHS(TxReadyHS),
        .TxReadyEsc(TxReadyEsc),
        .Direction(Direction),
        .Stopstate(Stopstate),
        .Esc_Sequencer_En(Esc_Sequencer_En),
        .Esc_Serializer_En(Esc_Serializer_En),
        .EscSerSeqSel(EscSerSeqSel),
        .Esc_Encoder_En(Esc_Encoder_En),
        .Esc_Sequences(Esc_Sequences),
        .TX_Ctrl_Out(TX_Ctrl_Out),
        .LpCtrlEscSel(LpCtrlEscSel),
        .LpTxEn(LpTxEn),
        .HsTxEn(HsTxEn),
        .LpRxEn(LpRxEn),
        .Esc_Decoder_En(Esc_Decoder_En),
        .Ctrl_Decoder_En(Ctrl_Decoder_En),
        .Sync(Sync),
        .Post(Post),
        .TxSendSynchS(TxSendSynchS),
        .TxSendSynchIS(TxSendSynchIS)
    );

    function bit Check_State(input [4:0] state);
        if(state == DUT.current_state) Check_State = 1;
        else                           Check_State = 0;
    endfunction
    
    task automatic assert_state(input [4:0] state);
        assert (Check_State(state)) else $error("Wrong State at time %0t, Expected state = %b, Current_State = %b", $time, state, DUT.current_state);
    endtask

    // Clock generation
    always begin
        clk = 1'b1;
        #(Clk_Period/2);
        clk = 1'b0;
        #(Clk_Period/2);
    end


    initial begin
        
        rst_n = 1'b0;
        TurnRequest = 0;
        TxRequestEsc = 0;
        TxRequestHS = 0;
        TxUlpsEsc = 0;
        TxLpdtEsc = 0;
        TxUlpsExit = 0;
        TxTriggerEsc = 4'b0;
        Pre_Done = 0;
        Sync_Done = 0;
        Post_Done = 0;
        Cmd_Done = 0;
        TxSendSyncHS = 0;
        Ctrl_Decoder_Out = 2'b00;
        ForceRxmode = 0;

        // Wait for reset to complete
        #(Clk_Period*2);
        rst_n = 1'b1;
        #(Clk_Period*2);
        assert_state(TX_STOP);

        //test case 1: HS Request
        $display("Test Case 1: HS Request");
        TxRequestHS = 1;
        #(Clk_Period*2); //10 to reach preamble + 13 to finish the preamble
        assert_state(TX_HS_REQUEST);
        #(Clk_Period*5);
        assert_state(TX_HS_PREPARE);
        #(Clk_Period*5);
        assert_state(TX_HS_PREAMBLE);
        #(Clk_Period*12);
        Pre_Done = 1;
        #(Clk_Period*2);
        assert_state(TX_HS_SYNC_WORD);
        Pre_Done = 0;
        #(Clk_Period*6);
        Sync_Done = 1;
        #(Clk_Period*2);
        assert_state(TX_HS_SEND_DATA);
        Sync_Done = 0;
        #(Clk_Period*32);
        TxRequestHS = 0;
        #(Clk_Period*7);
        assert_state(TX_HS_POST);
        Post_Done = 1;
        #(Clk_Period*2);
        assert_state(TX_STOP);
        Post_Done = 0;
        #(Clk_Period*10);

        $display("Test Case 2: Turn Around to RX_STOP");
        TurnRequest = 1;
        #(Clk_Period*2);
        assert_state(TX_LP_RQST);
        #(Clk_Period*5); // Timer timeout
        assert_state(TX_LP_YIELD);
        #(Clk_Period*5); // Timer timeout
        assert_state(TX_TA_REQUEST);
        #(Clk_Period*5); // Timer timeout
        assert_state(TX_TA_GO);
        #(Clk_Period*20); // Timer timeout
        assert_state(RX_TA_LOOK);
        Ctrl_Decoder_Out = 2'b11; // Simulate ACK
        #(Clk_Period*2);
        assert_state(RX_TA_ACK);
        Ctrl_Decoder_Out = 2'b00; // Simulate completion
        #(Clk_Period*2);
        assert_state(RX_STOP);
        TurnRequest = 0;
        Ctrl_Decoder_Out = 2'b00;
        #(Clk_Period*10);

        rst_n = 1'b0;
        // Wait for reset to complete
        #(Clk_Period*2);
        rst_n = 1'b1;
        #(Clk_Period*2);
        assert_state(TX_STOP);

        $display("Test Case 3: Escape Mode");
        TxRequestEsc = 1;
        #(Clk_Period*2);
        assert_state(TX_LP_RQST);
        #(Clk_Period*5); // Timer timeout
        assert_state(TX_LP_YIELD);
        #(Clk_Period*5); // Timer timeout
        assert_state(TX_ESC_RQST);
        #(Clk_Period*5); // Timer timeout
        assert_state(TX_ESC_GO);
        #(Clk_Period*5); // Timer timeout
        assert_state(TX_ESC_CMD);
        TxTriggerEsc = 4'b0001; // Reset trigger
        Cmd_Done = 1;
        #(Clk_Period*2);
        assert_state(TX_TRIGGERS);
        Cmd_Done = 0;
        TxRequestEsc = 0;
        #(Clk_Period*2);
        assert_state(TX_MARK);
        #(Clk_Period);
        assert_state(TX_STOP);
        TxTriggerEsc = 4'b0000;
        #(Clk_Period*10);

        $display("All assertions passed.");
        $stop;
    end

    // Monitor 
    initial begin
        $monitor("Time = %t, State = %h, TX_Ctrl_Out = %b, Direction = %b, Stopstate = %b",
            $time, DUT.current_state, TX_Ctrl_Out, Direction, Stopstate);
    end

endmodule