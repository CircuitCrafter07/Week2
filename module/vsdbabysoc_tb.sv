`timescale 1ns/1ps

module vsdbabysoc_tb;

  // DUT signals
  wire OUT;
  wire CLK;
  reg reset;
  reg VCO_IN;
  reg ENb_CP;
  reg ENb_VCO;
  reg REF;
  real VREFH;
  real VREFL;

  // Instantiate DUT
  vsdbabysoc dut (
    .OUT(OUT),
    .reset(reset),
    .VCO_IN(VCO_IN),
    .ENb_CP(ENb_CP),
    .ENb_VCO(ENb_VCO),
    .REF(REF),
    .VREFH(VREFH)
    // .VREFL(VREFL) -- your vsdbabysoc wrapper currently comments this
  );

  // Reference clock generation (simulate input REF ~ 50 MHz)
  initial begin
    REF = 0;
    forever #10 REF = ~REF; // 20 ns period
  end

  // Simulated VCO input toggle (like oscillator driving PLL)
  initial begin
    VCO_IN = 0;
    forever #5 VCO_IN = ~VCO_IN; // 100 MHz
  end

  // Stimulus sequence
  initial begin
    // Initialize
    reset   = 1;
    ENb_CP  = 1;
    ENb_VCO = 1;
    VREFH   = 1.0;  // High reference for DAC
    VREFL   = 0.0;  // Low reference (not passed into wrapper)

    // Apply reset
    #100;
    reset = 0;

    // Run for some time
    #5000;

    // Disable PLL
    ENb_VCO = 0;
    #200;

    // Re-enable PLL
    ENb_VCO = 1;
    #2000;

    // Finish
    $finish;
  end

  // Monitor outputs
  initial begin
    $monitor($time,,
      " reset=%b REF=%b VCO_IN=%b ENb_VCO=%b OUT=%f",
      reset, REF, VCO_IN, ENb_VCO, OUT);
  end

  // Waveform dump
  initial begin
    $dumpfile("vsdbabysoc_tb.vcd");
    $dumpvars(0, vsdbabysoc_tb);
  end

endmodule

