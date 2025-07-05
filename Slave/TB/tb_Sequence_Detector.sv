`timescale 1ns/1ps

module Sequence_Detector_tb;

    // Clock and reset
    logic RxSymClkHs = 0;
    logic RstN = 0;
    always #5 RxSymClkHs = ~RxSymClkHs;

    // DUT signals
    logic [2:0] RxSymbol;
    logic [3:0] DetectedSeq;
    logic syncErr;
    logic sotErr;

    // Instantiate DUT
    Sequence_Detector dut (
        .RxSymClkHs(RxSymClkHs),
        .RstN(RstN),
        .RxSymbol(RxSymbol),
        .DetectedSeq(DetectedSeq),
        .syncErr(syncErr),
        .sotErr(sotErr)
    );
    
    property preamble_check;
        @(posedge RxSymClkHs) ##1 (DetectedSeq == 4'b0001);
    endproperty
    
    property sync_check;
        @(posedge RxSymClkHs) ##1 (DetectedSeq == 4'b0010);
    endproperty 
       
    property false_sync_ERR_check;
        @(posedge RxSymClkHs) ##1 (syncErr == 0);
    endproperty
    property sync_ERR_check;
        @(posedge RxSymClkHs) ##1 (syncErr == 1);
    endproperty
    
    property post_check;
        @(posedge RxSymClkHs) ##1 (DetectedSeq == 4'b0100);
    endproperty

    initial begin
        // Initialize
        RxSymbol <= 3'd0;
        #10
        RstN <= 1;
        #20;
//==========================================================================
// ============================== Test 1 ===================================
//==========================================================================  
         //Full correct sequence
         $display("/n=== Test 1: Full correct sequence ===");
         
        // send Preamble sequence
        repeat (7) begin
            RxSymbol <= 3'd3;
            @(posedge RxSymClkHs);
        end
        
        assert property (preamble_check)
            else $error("Preamble not detected");
        
        //send Sync Word sequence
        RxSymbol <= 3'd3;
        @(posedge RxSymClkHs);
        
        repeat (5) begin
            RxSymbol <= 3'd4;
            @(posedge RxSymClkHs);
        end
        
        RxSymbol <= 3'd3;
        @(posedge RxSymClkHs);  
                      
        assert property (sync_check)
            else $error("sync not detected");
            
        assert property (false_sync_ERR_check)
            else $error("False sync error detected");
            
        // send Data
        RxSymbol <= 3'd2;
        @(posedge RxSymClkHs);        
        RxSymbol <= 3'd1;
        @(posedge RxSymClkHs);        
        RxSymbol <= 3'd0;
        @(posedge RxSymClkHs);        
        RxSymbol <= 3'd6;
        @(posedge RxSymClkHs);        
        RxSymbol <= 3'd5;
        @(posedge RxSymClkHs);
        RxSymbol <= 3'd0;
        @(posedge RxSymClkHs);
        RxSymbol <= 3'd2;
        @(posedge RxSymClkHs);

         // send post sequence
        repeat (7) begin
            RxSymbol <= 3'd4;
            @(posedge RxSymClkHs);
        end
       assert property (post_check)
            else $error("post not detected");
            
//==========================================================================
// ============================== Test 2 ===================================
//==========================================================================  

        // Test 2: with sync error
        $display("\n=== Test 2: Preamble with sync error ===");
        
        // send Preamble sequence
        repeat (7) begin
            RxSymbol <= 3'd3;
            @(posedge RxSymClkHs);
        end
        
        assert property (preamble_check)
            else $error("Preamble not detected");
        
                
        // send Sync Word sequence
        RxSymbol <= 3'd3;
        @(posedge RxSymClkHs);
        
        repeat (3) begin
            RxSymbol <= 3'd4;
            @(posedge RxSymClkHs);
        end
        
        RxSymbol <= 3'd3;
        @(posedge RxSymClkHs);
        
        assert property (sync_check)
            else $error("sync not detected");
            
        assert property (sync_ERR_check)
            else $error("sync error not detected");
          
         // send post sequence
        repeat (7) begin
            RxSymbol <= 3'd4;
            @(posedge RxSymClkHs);
        end
       assert property (post_check)
            else $error("post not detected");
            
//==========================================================================
// ============================== Test 3 ===================================
//==========================================================================  
        // Test 2: with sotErr and double packet of data and double sync word in the start and in the Mid 
         $display("/n=== Test 2: with sotErr ===");
         
        // send Preamble sequence
        repeat (7) begin
            RxSymbol <= 3'd3;
            @(posedge RxSymClkHs);
        end
        
        //assert (DetectedSeq == 3'b001) else $error("Preamble not detected");
        assert property (preamble_check)
            else $error("Preamble not detected");
        
        // send Sync Word sequence
        //RxSymbol <= 3'd3;
        //@(posedge RxSymClkHs);
        
        repeat (5) begin
            RxSymbol <= 3'd4;
            @(posedge RxSymClkHs);
        end
        
        RxSymbol <= 3'd3;
        @(posedge RxSymClkHs);  
                      
        assert property (sync_check)
            else $error("sync not detected");
            
        assert property (false_sync_ERR_check)
            else $error("False sync error detected");
            
        // send Data
        RxSymbol <= 3'd2;
        @(posedge RxSymClkHs);        
        RxSymbol <= 3'd1;
        @(posedge RxSymClkHs);        
        RxSymbol <= 3'd0;
        @(posedge RxSymClkHs);        
        RxSymbol <= 3'd6;
        @(posedge RxSymClkHs);        
        RxSymbol <= 3'd5;
        @(posedge RxSymClkHs);
        RxSymbol <= 3'd0;
        @(posedge RxSymClkHs);
        RxSymbol <= 3'd2;
        @(posedge RxSymClkHs);

        // send Sync Word sequence
        //RxSymbol <= 3'd3;
        //@(posedge RxSymClkHs);
        
        repeat (5) begin
            RxSymbol <= 3'd4;
            @(posedge RxSymClkHs);
        end
        
        RxSymbol <= 3'd3;
        @(posedge RxSymClkHs);  
                      
        assert property (sync_check)
            else $error("sync not detected");
            
        assert property (false_sync_ERR_check)
            else $error("False sync error detected");
            
        // send Data
        RxSymbol <= 3'd2;
        @(posedge RxSymClkHs);        
        RxSymbol <= 3'd1;
        @(posedge RxSymClkHs);        
        RxSymbol <= 3'd0;
        @(posedge RxSymClkHs);        
        RxSymbol <= 3'd6;
        @(posedge RxSymClkHs);        
        RxSymbol <= 3'd5;
        @(posedge RxSymClkHs);
        RxSymbol <= 3'd0;
        @(posedge RxSymClkHs);
        RxSymbol <= 3'd2;
        @(posedge RxSymClkHs);

         // send post sequence
        repeat (7) begin
            RxSymbol <= 3'd4;
            @(posedge RxSymClkHs);
        end
       assert property (post_check)
            else $error("post not detected");
     
        $display("\nAll test sequences completed successfully");
        $finish;
    end

    // Monitor
    always @(posedge RxSymClkHs) begin
        $display("Time: %0t State: %0d Symbol: %b Detected: %b Error: %b", 
                 $time, dut.state, RxSymbol, DetectedSeq, syncErr);
    end

endmodule