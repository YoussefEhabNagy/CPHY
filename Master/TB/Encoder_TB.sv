`timescale 1ns/1ps

module Encoder_TB;

  //signals
  logic        TxSymbolClkHS = 1;
  logic        reset;
  logic        EncoderEn;
  logic [2:0]  Sym;
  logic        PU_A, PD_A, PU_B, PD_B, PU_C, PD_C;

  // Clock generation
  parameter Clk_Period = 0.48;
  always #(Clk_Period/2) TxSymbolClkHS = ~TxSymbolClkHS;

  Encoder dut (
    .RstN(reset),
    .EncoderEn(EncoderEn),
    .TxSymbolClkHS(TxSymbolClkHS),
    .Sym(Sym),
    .A({PU_A,PD_A}),
    .B({PU_B,PD_B}),
    .C({PU_C,PD_C})
  );

  //During reset or when EncoderEn = 0, outputs must be all 1 (high-impedance)
  property safe_outputs_when_reset;
    @(posedge TxSymbolClkHS)
    (!reset) |-> (PU_A == 1'b0 && PD_A == 1'b1 &&
                  PU_B == 1'b0 && PD_B == 1'b1 &&
                  PU_C == 1'b0 && PD_C == 1'b1);
  endproperty

  property safe_outputs_when_disabled;
    @(posedge TxSymbolClkHS)
    (!EncoderEn) |=> (PU_A == 1'b0 && PD_A == 1'b1 &&
                      PU_B == 1'b0 && PD_B == 1'b1 &&
                      PU_C == 1'b0 && PD_C == 1'b1);
  endproperty

  //When Encoder is enabled, outputs must not all be 1's (they should actively drive valid state)
  property valid_outputs_when_enabled;
    @(posedge TxSymbolClkHS)
    (reset && EncoderEn) |=> (
                                (PU_A && !PD_A && !PU_B && PD_B && PU_C && PD_C) || //X+
                                (!PU_A && PD_A && PU_B && !PD_B && PU_C && PD_C) || //X-
                                (PU_A && PD_A && PU_B && !PD_B && !PU_C && PD_C) || //Y+
                                (PU_A && PD_A && !PU_B && PD_B && PU_C && !PD_C) || //Y-
                                (!PU_A && PD_A && PU_B && PD_B && PU_C && !PD_C) || //Z+
                                (PU_A && !PD_A && PU_B && PD_B && !PU_C && PD_C)    //Z-
                                );
  endproperty

  // Assertion 
  assert property (safe_outputs_when_reset) else $fatal("Outputs are not safe during reset!");
  assert property (safe_outputs_when_disabled) else $fatal("Outputs are not safe during disabled!");
  assert property (valid_outputs_when_enabled) else $fatal("Outputs did not drive active states when enabled!");

  initial begin
    
    reset     = 0;
    EncoderEn = 0;
    Sym       = 3'b000;

    #(Clk_Period);
    reset = 1;

    @(posedge TxSymbolClkHS);

    EncoderEn = 1;

    repeat(2) begin
      @(posedge TxSymbolClkHS);
      Sym = 3'b000; // Rotate CCW, same polarity
    end

    @(posedge TxSymbolClkHS);
    Sym = 3'b001;   // Rotate CCW, opposite polarity

    @(posedge TxSymbolClkHS);
    Sym = 3'b010;   // Rotate CW, same polarity

    @(posedge TxSymbolClkHS);
    Sym = 3'b011;   // Rotate CW, opposite polarity

    @(posedge TxSymbolClkHS);
    Sym = 3'b100;   // Same phase, opposite polarity

    @(posedge TxSymbolClkHS);
    EncoderEn = 0;  

    #(Clk_Period*10);

    $display("All assertions passed. Test completed successfully.");
    $stop;
  end

endmodule
