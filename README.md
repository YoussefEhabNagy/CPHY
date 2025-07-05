# MIPI C-PHY Encoder Project

## Overview

This project implements a **MIPI C-PHY v1.0 transmitter subsystem** in Verilog/SystemVerilog, including core components such as the Encoder, Serializer, and HS/Escape Sequencers. It targets high-speed serial communication typically used in camera and display interfaces for mobile and embedded systems. The design is developed with verification and synthesis readiness in mind, aligning with the industry's best practices.

---

## 📁 Project Structure

```
Master/
├── Data/                 # VS Code settings and notes
│   └── Reed_Me.txt       # Preliminary notes
├── Docs/                 # Component PDFs (docs & diagrams)
│   ├── Encoder.pdf
│   ├── Escape Encoder.pdf
│   ├── HS_Sequencer.pdf
│   ├── Spyglass CDC.pdf
│   └── ...
├── Rtl/                  # RTL implementation (Verilog/SystemVerilog)
│   ├── Encoder.sv
│   ├── HS_Sequencer.v
│   ├── Esc_Sequencer.v
│   └── ...
├── Sim/                  # Testbenches and assertions (SystemVerilog)
│   ├── tb_Encoder.sv
│   ├── tb_HS_Sequencer.sv
│   ├── tb_Esc_Sequencer.sv
│   └── ...
├── Synth/                # Synthesis scripts/reports
│   └── ...
└── Spyglass/             # CDC and Lint setup
    ├── spyglass.prj
    ├── spyglass.rtl
    └── reports/
```

---

## 🔍 Project Phases

1. **Standard Familiarization**
   - MIPI C-PHY v1.0 specification study
2. **Architecture and FSM Design**
   - Block-level architecture and finite state machines
3. **RTL Implementation**
   - Verilog/SystemVerilog modules including:
     - `Encoder`
     - `HS_Sequencer`
     - `Esc_Sequencer`
     - Serializers, Mappers, and more
4. **Integration**
   - Module interfacing and end-to-end flow setup
5. **SpyGlass Static Checks**
   - CDC and lint checks
6. **Synthesis and DFT**
   - Netlist generation and testability enhancements

---

## ⚙️ Key Modules

- **Encoder**: Converts 16-bit parallel data to 3-wire MIPI C-PHY symbols following 2.28 bits/symbol efficiency.
- **HS_Sequencer**: Orchestrates Pre, Sync, and Post sequences using `SeqDone` signal feedback.
- **Esc_Sequencer**: Sends 8-bit predefined escape commands MSB-first with timing alignment.
- **Serializers**: Convert parallel symbols into serial PU/PD control logic to drive analog drivers.
- **Contention Detection**: Ensures TX line stability and safety during simultaneous driver activity.

---

## ✅ Verification

- **Testbenches**: SystemVerilog-based with UVM-independent manual environments.
- **Assertions (SVA)**: Cover reset, enable/disable states, and correct encoding behavior.
- **Formal Readiness**: Design is modular and can be plugged into formal tools.

---

## 🧪 Tools Used

- **Design**: SystemVerilog / Verilog
- **Simulation**: Vivado / QuestaSim (or any simulator with SV support)
- **Synthesis**: Design Compiler
- **Static Checks**: SpyGlass for CDC and lint
- **Editor**: VS Code + Verilog extensions

---

## 🚀 Getting Started

1. Open the project in Vivado for the waveform.
2. Navigate to `Sim/` and run the testbench:
   ```sh
   vsim -do Sim/Master_tb.sv
   ```
3. load then Review waveform outputs and assertion passes.
4. For synthesis, use your tool’s GUI or TCL interface with the `Synth/` scripts.

---

## 🙏 Acknowledgments

Special thanks to:
- **Si-Vision** – for mentoring during the graduation project
- **ITI Digital IC Design Program** – for technical training and project guidance

---

## 📌 Notes

- Default states like `X+` were chosen arbitrarily unless specified in the spec.
- All PU/PD outputs are intended to interface analog driver MOSFETs.
- CDC signals (e.g., `EscEncoderEn`) are synchronized explicitly and verified in SpyGlass.

