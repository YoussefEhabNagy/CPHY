//=================================================================================================
//  File Name    : Lp_Test_Tb.sv
//  Description  : 
//      This testbench verifies the Escape Decoder module working alongside the Low Power Clock 
//      Recovery block. It applies a variety of escape commands and monitors outputs to validate 
//      the correct detection of low power data mode, ultra low power mode, reset trigger, and 
//      error conditions such as invalid commands, wrong bit counts, and control sequence errors.
//
//  Key Inputs   :
//      - A, B, C           : Escape decoder input signals
//      - RST               : Reset signal
//      - EscDecoderEn      : Escape decoder enable signal
//      - RequestDetection  : Request detection trigger signal
//
//  Key Outputs  :
//      - RxLpdtEsc         : Low power data mode detected flag
//      - RxUlpsEsc         : Ultra low power mode detected flag
//      - RxTriggerEsc      : Reset trigger detected flag
//      - EscBit            : Decoded data bit output
//      - ErrControl        : Control sequence error flag
//      - ErrSyncEsc        : Synchronization error flag (wrong bit count)
//      - ErrEsc            : Invalid escape command error flag
//      - LpFsmStop         : Escape mode FSM stop flag
//
//  Tests        :
//      - Low Power Data Mode:
//          Sends the low power data command and verifies correct detection and data reception.
//      - Ultra Low Power Mode:
//          Sends the ultra low power command and verifies proper detection of ULPS mode.
//      - Reset Trigger:
//          Sends reset trigger command and checks for trigger detection output.
//      - Invalid Command:
//          Sends an invalid command and expects the ErrEsc flag to be asserted.
//      - Low Power Data with Wrong Bit Count:
//          Sends low power data command followed by incorrect data bit count and verifies error detection.
//      - Control Sequence Error:
//          Simulates wrong control sequences and expects the ErrControl flag assertion.
//
//  Author      : Amira Khaled
//  Date        : 25/05/2025
//=================================================================================================

module Lp_Test_Tb();

    reg A;
    reg B;
    reg C;
    reg RST;
    reg EscDecoderEn;
    reg RequestDetection;
    wire RxLpdtEsc;
    wire RxUlpsEsc;
    wire [3:0] RxTriggerEsc;
    wire EscBit;  //output data
    wire ErrControl; //wrong control sequence
    wire ErrSyncEsc; //wrong number of bits
    wire ErrEsc; //wrong command
    wire LpFsmStop; //End of the escape mode

    Lp_Test DUT (
    .A(A),
    .B(B),
    .C(C),
    .RST(RST),
    .EscDecoderEn(EscDecoderEn),
    .RequestDetection(RequestDetection),
    .RxLpdtEsc(RxLpdtEsc),
    .RxUlpsEsc(RxUlpsEsc),
    .RxTriggerEsc(RxTriggerEsc),
    .EscBit(EscBit),  //output data
    .ErrControl(ErrControl), //wrong command
    .ErrSyncEsc(ErrSyncEsc), //wrong number of bits
    .ErrEsc(ErrEsc),
    .LpFsmStop(LpFsmStop)
    );

    initial begin
        $display("Start test low power data mode at %0t", $time);
        initialize();
        EscapeEntry();
        Commandsend(8'b11100001); //Low power data command
        assert (RxLpdtEsc && !RxUlpsEsc && !RxTriggerEsc[0]) else $error("Low power data command faild");
        Data_random(8); //Right number of bits
        $display("Receiving data done at %0t", $time);
        space(); //no receving data but the escape decoder is still enabled
        EndEscape();
        assert (LpFsmStop) else $error("Stop state detection faild at %0t", $time);
        $display ("[Pass] Testing Low power data receving at %0t", $time);
        #(5);

        $display("Start test Ultra low power mode at %0t", $time);
        initialize();
        EscapeEntry();
        Commandsend(8'b00011110); //Ultra low power command
        assert (!RxLpdtEsc && RxUlpsEsc && !RxTriggerEsc[0]) else $error("Ultra low power command faild");
        #(20);
        EndEscape();
        $display ("[Pass] Testing Ultra low power mode at %0t", $time);
        #(5);

        $display("Start test Reset trigger at %0t", $time);
        initialize();
        EscapeEntry();
        Commandsend(8'b01100010); //Reset Trigger command
        assert (!RxLpdtEsc && !RxUlpsEsc && RxTriggerEsc[0]) else $error("Reset Trigger command faild");
        #(20);
        EndEscape();
        $display ("[Pass] Testing Reset trigger at %0t", $time);
        #(5);

        $display("Start test wrong command at %0t", $time);
        initialize();
        EscapeEntry();
        Commandsend(8'b01100011); 
        assert (!RxLpdtEsc && !RxUlpsEsc && !RxTriggerEsc[0] && ErrEsc) else $error("Unvalid command detection faild");
        #(20);
        EndEscape();
        $display ("[Pass] Testing wrong command at %0t", $time);
        #(5);

        $display("Start test low power data mode with wrong number of bits at %0t", $time);
        initialize();
        EscapeEntry();
        Commandsend(8'b11100001); //Low power data command
        assert (RxLpdtEsc && !RxUlpsEsc && !RxTriggerEsc[0]) else $error("Low power data command faild");
        Data_random(7); //Right number of bits
        $display("Receiving data done at %0t", $time);
        space(); //no receving data but the escape decoder is still enabled
        EndEscape();
        assert (LpFsmStop) else $error("Stop state detection faild at %0t", $time);
        assert (ErrSyncEsc) else $error("Error Sync Escape detection faild at %0t", $time);
        $display ("[Pass] Testing low power data mode with wrong number of bits at %0t", $time);
        #(5);

        $display("Start testing Control sequence error");
        initialize();
        wrong_controls();
        assert(ErrControl) else $error("Error control detection faild at %0t", $time);
        $display("[Pass] Testing Control sequence error at %0t", $time);    

        #(20)
        $stop;
    end
    

    task initialize; 
    begin
        A = 1; B = 1; C = 1;
        RST = 0;
        EscDecoderEn = 0;
        RequestDetection = 0;
        #(10);
    end
    endtask

    task EscapeEntry; 
    begin
        RST = 1;
        RequestDetection = 1;
        A = 1; B = 0; C = 0;
        #(5);
        A = 0; B = 0; C = 0;
        #(5);
        A = 0; B = 0; C = 1;
        #(5);
        A = 0; B = 0; C = 0;
        EscDecoderEn = 1;
        RequestDetection = 0;
        #(5);
    end
    endtask

    task Commandsend(input [7:0] comma);
    integer i;
    begin
        for (i=7; i>=0; i=i-1)
        begin
        A = comma [i];
        C = ~comma [i];
        #(5);
        A = 0; B = 0; C = 0;
        #(5);
        end
        if (comma != 8'b11100001) begin
            EscDecoderEn = 1'b0;
        end
    end
    endtask

    task Data_random (input integer a);
    integer i;
    begin
        for (i = 0; i < a ; i=i+1)
        begin
        A = {$random}%2;
        B = 0;
        C = ~A;
        #(5)
        assert (EscBit == A) else $error("Unexpected output data, Expected output = %b, Output = %b, Time = %0t", A, EscBit, $time); 
        A = 0;
        B = 0;
        C = 0;
        #(5);
        end      
    end
    endtask

    task space;
    begin
    repeat(5)
    begin
       A = 0; B = 0; C = 0;
       assert (!DUT.RxClkEsc) else $error("There is clock while receiving space!!");
       #(5);
    end
    end
    endtask
    
    task EndEscape;
    begin   
        A = 1; B = 0; C = 0; 
        #(5);
        A = 1; B = 1; C = 1;
        #(5);
    end
    endtask

    task wrong_controls;
    begin
        RequestDetection = 1;
        A = 1; B = 0; C = 0; 
        #(5);
        A = 1; B = 1; C = 1;  
        #(5);
    end
    endtask

endmodule