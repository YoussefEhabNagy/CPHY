`timescale 1ns/1ps

module Esc_Sequencer_TB;

  // Testbench signals
  logic        TxClkEsc = 1;
  logic        reset;
  logic        EscSeqEn;
  logic [2:0]  EscSeqCtr;
  logic        SeqBit;
  logic        CmdDone;

  // Clock generation
  parameter Clk_Period = 10;
  always #(Clk_Period/2) TxClkEsc = ~TxClkEsc;

  // DUT instantiation
  Esc_Sequencer dut (
    .reset(reset),
    .TxClkEsc(TxClkEsc),
    .EscSeqEn(EscSeqEn),
    .EscSeqCtr(EscSeqCtr),
    .SeqBit(SeqBit),
    .CmdDone(CmdDone)
  );

  // Assertion properties
  property cmd_done_assertion;
    @(posedge TxClkEsc) disable iff (!reset)
    (EscSeqEn && (dut.Count == 3'd0) && (CmdDone == 1'b0))
    |=> ##7 (CmdDone == 1'b1);
  endproperty

  // Assertion instance
  assert property (cmd_done_assertion) else $fatal("CmdDone did not assert after 7 cycles");

  // Stimulus
  initial begin
    // Initialize signals
    reset    = 0;
    EscSeqEn = 0;
    EscSeqCtr = 3'd0;

    // Apply reset
    #(Clk_Period);
    reset = 1;

    @(posedge TxClkEsc);
    
    // Start sequence
    EscSeqEn = 1;
    EscSeqCtr = 3'd0; // Select CMD[2]

    // Keep enable high for 8 clock cycles
    #(Clk_Period*9);

    // Disable sequence after 8 cycles
    EscSeqEn = 0;

    #(Clk_Period*20);

    $display("All assertions passed.");
    $stop;
  end

endmodule
