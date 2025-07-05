`timescale 1ns/1ps

module HS_Sequencer_TB;

  // Testbench signals
  logic        SymClk = 1;
  logic        reset;
  logic        Sequencer_En;
  logic        Sync;
  logic        Post;
  logic        Pre_Done;
  logic        Sync_Done;
  logic        Post_Done;
  logic [2:0]  SeqSym;

  // Clock generation
  parameter Clk_Period = 10;
  always #(Clk_Period/2) SymClk = ~SymClk;

  // DUT instantiation
  HS_Sequencer dut (
    .reset(reset),
    .SymClk(SymClk),
    .Sequencer_En(Sequencer_En),
    .Sync(Sync),
    .Post(Post),
    .Pre_Done(Pre_Done),
    .Sync_Done(Sync_Done),
    .Post_Done(Post_Done),
    .SeqSym(SeqSym)
  );


  // Assertion properties
  property pre_done_assertion;
    @(posedge SymClk) disable iff (!reset)
    ((Sync == 1'b0) && (Post == 1'b0) && (Sequencer_En == 1'b1) && (dut.Count == 4'b0000) && (Pre_Done == 1'b0)) 
    |=> ##12 (Pre_Done == 1'b1);
  endproperty

  property sync_done_assertion;
    @(posedge SymClk) disable iff (!Sequencer_En)
    ((Sync == 1'b1) && (Post == 1'b0) && (Sequencer_En == 1'b1)) 
    |=> ##6 Sync_Done == 1'b1;
  endproperty

  property post_done_assertion;
    @(posedge SymClk) disable iff (!Sequencer_En)
    ((Sync == 1'b0) && (Post == 1'b1) && (Sequencer_En == 1'b1)) 
    |=> ##6 Post_Done == 1'b1;
  endproperty

  // Assertion instances
  assert property (pre_done_assertion) else $fatal("Pre_Done did not assert after 12 cycles");
  assert property (sync_done_assertion) else $fatal("Sync_Done did not assert after 6 cycles");
  assert property (post_done_assertion) else $fatal("Post_Done did not assert after 6 cycles");


  initial begin

    Sequencer_En = 0;
    Sync = 0;
    Post = 0;
    reset = 0;

    #10;

    reset = 1;

    
    @(posedge SymClk);

    Sequencer_En = 1;

    /// Preamble phase ///
    #(Clk_Period*14)

    /// Sync phase ///
    Sync = 1;
    Post = 0;

    #(Clk_Period*7)

    Sequencer_En = 0;
    Sync = 0;
    Post = 0;
    
    #(Clk_Period*30)

    Sequencer_En = 1;
    Sync = 1;
    Post = 0;

    #(Clk_Period*7)

    Sequencer_En = 0;
    Sync = 0;
    Post = 0;
    
    #(Clk_Period*30)
    /// Post phase ///
    Sync = 0;
    Post = 1;
    
    #(Clk_Period*5)
    $display("All assertions passed.");
    $stop;
  end

endmodule
