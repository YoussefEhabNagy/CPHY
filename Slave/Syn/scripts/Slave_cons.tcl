# ---- Budget Clock --- # 

set Clk_Esc  100;    # 10Mhz
set Clk_Symbol  1;       # 1.05 Ghz
set Clk_word 7 ;    # 150Mhz

# -------the timing in ns
#  input clocks
create_clock -name RxClkFsm -period $Clk_word  [get_ports RxClkFsm]
create_clock -name TxClkEsc -period $Clk_Esc   [get_ports TxClkEsc]
#  generated clock in our modules
# HS clk
create_clock -name RxSymClkHS -period $Clk_Symbol   [get_pins clk_gating/GCLK] ;#  lp_out_Clk ----> esc_DecoderClk   ESc_DesClk
create_generated_clock -name RxWordClkHS -source [get_pins clk_gating/GCLK] -divide_by 7  [get_pins wordclk/RxWordClkHs]  ; # note that there a relation between sym &word clocks
# lp clk
create_clock -name RxClkEsc -period $Clk_Esc   [get_pins clk_recovery_lp/RxClkEsc]

set_clock_groups -asynchronous -group {RxClkFsm} -group {TxClkEsc} -group {RxSymClkHS RxWordClkHS} -group {RxClkEsc}




# --------jitter and skew

set  delay1  [expr 0.05*$Clk_Esc]
set  delay2  [expr 0.1*$Clk_Symbol]
set  delay3  [expr 0.1*$Clk_word]
 

set_clock_uncertainty  $delay1 [get_ports  TxClkEsc]
set_clock_uncertainty  $delay1 [get_pins  clk_recovery_lp/RxClkEsc]
				
set_clock_uncertainty  $delay2  [get_pins clk_gating/GCLK]
set_clock_uncertainty  $delay3 [get_ports { RxClkFsm}]
set_clock_uncertainty  $delay3 [get_pins wordclk/RxWordClkHs]





# ---- Model external ---- #
set in1_delay  [expr 0.1*$Clk_Esc]
set out1_delay [expr 0.1*$Clk_Esc]
set in2_delay  [expr 0.15*$Clk_Symbol]
set out2_delay [expr 0.15*$Clk_Symbol]
set in3_delay  [expr 0.15*$Clk_word]
set out3_delay [expr 0.15*$Clk_word]


#----------TA input ports
set TA_in [list TxReqEsc TxLpdtEsc TxUlpsEsc TxUlpsExit TxTriggerEsc* TxValidEsc]
# ---------TA output ports
set TA_out [list TxReadyEsc LpTx* LpTxEn ErrContentionLP0 ErrContentionLP1]


# ---- delay for FsmSlave Signals ---#
set_input_delay -max $in3_delay -clock [get_clocks RxClkFsm] [get_ports {ForceRxmode TurnDisable ForceTxStopmode Enable }]
set_output_delay -max $out3_delay -clock [get_clocks RxClkFsm] [remove_from_collection [all_outputs] [get_ports {RxWordClkHS_out RxClkEsc  RxEscData* RxDataHS*  TxReadyEsc LpTx* LpTxEn ErrContentionLP0 ErrContentionLP1}]]
# ----- delay for TurnAround Signals
set_input_delay -max $in1_delay -clock [get_clocks TxClkEsc] [get_ports $TA_in]
set_output_delay -max $out1_delay -clock [get_clocks TxClkEsc] [get_ports $TA_out]

#---delay for HS
set_input_delay -max $in2_delay -clock [get_clocks RxSymClkHS] [get_ports {A B}] ; #  A B must delayed with the fastest clk to avoid violates
set_output_delay -max $out2_delay -clock [get_clocks RxSymClkHS] [get_ports {RxDataHS*}]
# ---- delay for lp
set_output_delay -max $out1_delay -clock [get_clocks RxClkEsc] [get_ports {RxEscData*}]


# ----or we can use this-------
# --- input constrain
set_driving_cell -lib_cell IBUFFX4_LVT -pin Y [get_ports [remove_from_collection [all_inputs] [get_ports {RxClkFsm TxClkEsc}]]];  # To determined input transition   Err: Cannot find the specified driving cell in memory.   (UID-993)


# --- output constrain
set_load 0.2 [remove_from_collection [all_outputs] [get_ports {RxWordClkHS_out RxClkEsc }]]

# ---- Optimizations  ---- #
# Input to register
#set_max_delay 10 -from [all_inputs] -to [all_registers]
#set_min_delay 0.5  -from [all_inputs] -to [all_registers]

# Register to output
#set_max_delay 13 -from [all_registers] -to [all_outputs]
#set_min_delay 0.5 -from [all_registers] -to [all_outputs]

# Register to register
#set_max_delay 10 -from [all_registers] -to [all_registers]
#set_min_delay 0.5 -from [all_registers] -to [all_registers]
 


# ---- Constraints 
#set_max_transition 0.5 [all_outputs -of [all_registers -clock [get_clocks RxSymClkHS]]]

#set_max_transition .4 [get_clocks]
#set_max_capcitance .08
#set_min_capcitance .08

#set_max_fanout 4 ; # Err: Required argument 'object_list' was not found (CMD-007)
#set_max_fanout 4 [get_cells -hierarchical *]




# Area max  
set_max_area  0


# --- power
#set_max_dynamic_power 10   
#set_max_static_power  0
#set_optimize_registers true




# ---- Exceptions --- #
#set_false_path -hold -from [remove_from_collection [all_inputs] [get_ports RxClkFsm]]
#set_false_path -hold -to [all_outputs]


# ----- to prevent tool to optimize this path
# Protect all clocks
set_dont_touch_network [get_clocks]    ;    # overriding warning

# Protect reset network
set_dont_touch_network [get_ports RstN] ; # overriding warning



# ---- Load Model ---- #
#set_wire_load_model -name  8000  -library  saed32lvt_dlvl_ff1p16v25c_ip16v
