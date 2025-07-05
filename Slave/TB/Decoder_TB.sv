`timescale 1ns/1ps

module Decoder_TB;

  // Signals
  logic        RxSymbolClkHS = 0;
  logic        reset;
  logic        DecoderEn;
  logic [2:0]  State;
  logic [2:0]  Sym;

  // Clock generation
  parameter Clk_Period = 10;
  always #(Clk_Period/2) RxSymbolClkHS = ~RxSymbolClkHS;


  Decoder dut (
    .reset(reset),
    .DecoderEn(DecoderEn),
    .RxSymbolClkHS(RxSymbolClkHS),
    .State(State),
    .Sym(Sym)
  );

  reg [2:0] PS; 

  // Property definitions
  property reset_output;
    @(posedge RxSymbolClkHS)
    (!reset) |-> (Sym == 3'b000);
  endproperty

  property disabled_output;
    @(posedge RxSymbolClkHS)
    (!DecoderEn) |=> (Sym == 3'b000);
  endproperty

  property valid_outputs_when_enabled;
    @(posedge RxSymbolClkHS)
    (reset && DecoderEn) |=> (Sym inside {3'b000, 3'b001, 3'b010, 3'b011, 3'b100});
  endproperty

  property decoding_ccw_same;
    @(posedge RxSymbolClkHS)
    (reset && DecoderEn && (State == {PS[1:0], PS[2]})) |=> (Sym == 3'b000);
  endproperty

  property decoding_ccw_opposite;
    @(posedge RxSymbolClkHS)
    (reset && DecoderEn && (State == ~{PS[1:0], PS[2]})) |=> (Sym == 3'b001);
  endproperty

  property decoding_cw_same;
    @(posedge RxSymbolClkHS)
    (reset && DecoderEn && (State == {PS[0], PS[2:1]})) |=> (Sym == 3'b010);
  endproperty

  property decoding_cw_opposite;
    @(posedge RxSymbolClkHS)
    (reset && DecoderEn && (State == ~{PS[0], PS[2:1]})) |=> (Sym == 3'b011);
  endproperty

  property decoding_opposite_polarity;
    @(posedge RxSymbolClkHS)
    (reset && DecoderEn && (State == ~PS)) |=> (Sym == 3'b100);
  endproperty

  // Assertion
  assert property (reset_output) else $error("Outputs are not right during reset!");
  assert property (disabled_output) else $error("Outputs are not right during disabled!");
  assert property (valid_outputs_when_enabled) else $error("Outputs did not drive valid states when enabled!");

  assert property (decoding_ccw_same) else $error("Incorrect decoding for CCW same polarity!");
  assert property (decoding_ccw_opposite) else $error("Incorrect decoding for CCW opposite polarity!");
  assert property (decoding_cw_same) else $error("Incorrect decoding for CW same polarity!");
  assert property (decoding_cw_opposite) else $error("Incorrect decoding for CW opposite polarity!");
  assert property (decoding_opposite_polarity) else $error("Incorrect decoding for opposite polarity!");


always @(posedge RxSymbolClkHS, negedge reset) begin
    if(!reset) PS <= 011;
    else       PS <= State;
end

  initial begin
    
    reset    = 0;
    DecoderEn = 0;
    State    = 3'b100;
    
    
    #(Clk_Period);
    reset = 1;
    
    
    @(posedge RxSymbolClkHS);
    
    //Some transitions for the symbols to be reasonable

    // Rotate CCW, Opposite Polarity (Sym = 001)
    State = ~{PS[1:0], PS[2]}; 
    @(posedge RxSymbolClkHS);
    // Rotate CCW, Opposite Polarity (Sym = 001)
    State = ~{PS[1:0], PS[2]}; 
    @(posedge RxSymbolClkHS);
    // Rotate CCW, Opposite Polarity (Sym = 001)
    State = ~{PS[1:0], PS[2]}; 
    @(posedge RxSymbolClkHS);
    
    DecoderEn = 1;
    
    // Test all decoding cases
    // Rotate CCW, Same Polarity (Sym = 000)
    State = {PS[1:0], PS[2]}; 
    @(posedge RxSymbolClkHS);
    
    // Rotate CCW, Opposite Polarity (Sym = 001)
    State = ~{PS[1:0], PS[2]};
    @(posedge RxSymbolClkHS);
    
    
    // Rotate CW, Same Polarity (Sym = 010)
    State = {PS[0], PS[2:1]}; 
    @(posedge RxSymbolClkHS);
    
    
    // Rotate CW, Opposite Polarity (Sym = 011)
    State = ~{PS[0], PS[2:1]}; 
    @(posedge RxSymbolClkHS);
    
    
    // Same phase, Opposite polarity (Sym = 100)
    State = ~PS;
    @(posedge RxSymbolClkHS);
    
    
    DecoderEn = 0;
    @(posedge RxSymbolClkHS);
    
    #(Clk_Period*5);
    
    $display("All assertions passed. Test completed successfully.");
    $stop;
  end

endmodule