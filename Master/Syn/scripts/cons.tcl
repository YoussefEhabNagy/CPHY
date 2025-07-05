
####################################################################################
# Constraints
# ----------------------------------------------------------------------------
#
# 1. Generated Clock Definitions
#
# 2. set input/output delay on ports
#
# 3. Driving cells
#
# 4. Output load


####################################################################################
           #########################################################
                  #### Section 1 : Clock Definition ####
           #########################################################
#################################################################################### 
# 1. Master Clock Definitions 
# 2. Clock Uncertainties 
# 3. Clock Transitions
# 4. Clock Latencies
# 5. Clock groups
####################################################################################

# TX_Escape Clock (10 MHz)
set TX_ESC_CLK_NAME ESC_CLK
set TX_ESC_CLK_PER 100.0

set TX_CLK_ESC_SETUP_SKEW 0.2
set TX_CLK_ESC_HOLD_SKEW 0.1

set TX_CLK_ESC_RISE 0.8
set TX_CLK_ESC_FALL 0.8

set TX_CLK_ESC_LAT  1.5
# Symbol Clock (2.1 GHz)
set SYM_CLK_NAME SYM_CLK
#set SYM_CLK_PER [expr 1000.0 / 2100.0] ;# ≈ 0.4762 ns
set SYM_CLK_PER 1

set CLK_SYM_SETUP_SKEW 0.05
set CLK_SYM_HOLD_SKEW 0.025

set CLK_SYM_RISE 0.05
set CLK_SYM_FALL 0.05

set CLK_SYM_LAT  0.05
# Word Clock (300 MHz)
set WORD_CLK_NAME WORD_CLK
#set WORD_CLK_PER [expr 1000.0 / 300.0] ;# ≈ 3.333 ns
set WORD_CLK_PER 7
set CLK_WORD_SETUP_SKEW 0.2
set CLK_WORD_HOLD_SKEW 0.05

set CLK_WORD_RISE 0.15
set CLK_WORD_FALL 0.15

set CLK_WORD_LAT  0.8

# RX_Escape Clock (10 MHz)
set RX_ESC_CLK_NAME RX_ESC_CLK
set RX_ESC_CLK_PER 100.0

set RX_CLK_ESC_SETUP_SKEW 0.2
set RX_CLK_ESC_HOLD_SKEW 0.1

set RX_CLK_ESC_RISE 0.8
set RX_CLK_ESC_FALL 0.8

set RX_CLK_ESC_LAT  1.5

# 1. Master Clocks Definitions 
create_clock -name $TX_ESC_CLK_NAME -period $TX_ESC_CLK_PER [get_ports TxClkEsc]

create_clock -name $SYM_CLK_NAME    -period $SYM_CLK_PER [get_ports TxSymbolClkHS]

create_clock -name $WORD_CLK_NAME   -period $WORD_CLK_PER [get_ports TxWordClkHs]

create_clock -name $RX_ESC_CLK_NAME -period $RX_ESC_CLK_PER   [get_pins clk_recovery_lp/RxClkEsc]
# 2. Clock Uncertainties
set_clock_uncertainty -setup $TX_CLK_ESC_SETUP_SKEW [get_clocks $TX_ESC_CLK_NAME]
set_clock_uncertainty -hold  $TX_CLK_ESC_HOLD_SKEW  [get_clocks $TX_ESC_CLK_NAME]

set_clock_uncertainty -setup $CLK_SYM_SETUP_SKEW [get_clocks $SYM_CLK_NAME]
set_clock_uncertainty -hold  $CLK_SYM_HOLD_SKEW  [get_clocks $SYM_CLK_NAME]

set_clock_uncertainty -setup $CLK_WORD_SETUP_SKEW [get_clocks $WORD_CLK_NAME]
set_clock_uncertainty -hold  $CLK_WORD_HOLD_SKEW  [get_clocks $WORD_CLK_NAME]

set_clock_uncertainty -setup $RX_CLK_ESC_SETUP_SKEW [get_clocks $RX_ESC_CLK_NAME]
set_clock_uncertainty -hold  $RX_CLK_ESC_HOLD_SKEW  [get_clocks $RX_ESC_CLK_NAME]

# 3. Clock Transitions
set_clock_transition -rise $TX_CLK_ESC_RISE  [get_clocks $TX_ESC_CLK_NAME]
set_clock_transition -fall $TX_CLK_ESC_FALL  [get_clocks $TX_ESC_CLK_NAME]

set_clock_transition -rise $CLK_SYM_RISE  [get_clocks $SYM_CLK_NAME]
set_clock_transition -fall $CLK_SYM_FALL  [get_clocks $SYM_CLK_NAME]

set_clock_transition -rise $CLK_WORD_RISE  [get_clocks $WORD_CLK_NAME]
set_clock_transition -fall $CLK_WORD_FALL  [get_clocks $WORD_CLK_NAME]

set_clock_transition -rise $RX_CLK_ESC_RISE  [get_clocks $RX_ESC_CLK_NAME]
set_clock_transition -fall $RX_CLK_ESC_FALL  [get_clocks $RX_ESC_CLK_NAME]
# 4. Clock Latencies
set_clock_latency $TX_CLK_ESC_LAT [get_clocks $TX_ESC_CLK_NAME]

set_clock_latency $CLK_SYM_LAT [get_clocks $SYM_CLK_NAME]

set_clock_latency $CLK_WORD_LAT [get_clocks $WORD_CLK_NAME]

set_clock_latency $RX_CLK_ESC_LAT [get_clocks $RX_ESC_CLK_NAME]

# 5. Clock groups
set_clock_groups -asynchronous -group [get_clocks RX_ESC_CLK] -group [get_clocks WORD_CLK]
set_clock_groups -asynchronous -group [get_clocks ESC_CLK] -group [get_clocks WORD_CLK]
set_clock_groups -asynchronous -group [get_clocks ESC_CLK] -group [get_clocks SYM_CLK]
set_clock_groups -asynchronous -group [get_clocks WORD_CLK] -group [get_clocks SYM_CLK]
set_clock_groups -asynchronous -group [get_clocks WORD_CLK] -group [get_clocks ESC_CLK]
set_clock_groups -asynchronous -group [get_clocks WORD_CLK] -group [get_clocks RX_ESC_CLK]

####################################################################################
           #########################################################
             #### Section 2 : set input/output delay on ports ####
           #########################################################
####################################################################################

set in1_delay  [expr 0.2*$WORD_CLK_PER]
set out1_delay [expr 0.2*$WORD_CLK_PER]

set in2_delay  [expr 0.2*$TX_ESC_CLK_PER]
set out2_delay [expr 0.2*$TX_ESC_CLK_PER]

set in3_delay  [expr 0.2*$SYM_CLK_PER]
set out3_delay [expr 0.2*$SYM_CLK_PER]

set in4_delay  [expr 0.2*$RX_ESC_CLK_PER]
set out4_delay  [expr 0.2*$RX_ESC_CLK_PER]
#Constrain Input Paths
set_input_delay $in1_delay -clock $WORD_CLK_NAME [get_port TxDataHS]
set_input_delay $in1_delay -clock $WORD_CLK_NAME [get_port TxSendSyncHS]
set_input_delay $in1_delay -clock $WORD_CLK_NAME [get_port TxReqHS]
set_input_delay $in1_delay -clock $WORD_CLK_NAME [get_port TxReqEsc]
set_input_delay $in1_delay -clock $WORD_CLK_NAME [get_port TxLpdtEsc]
set_input_delay $in1_delay -clock $WORD_CLK_NAME [get_port TxUlpsEsc]
set_input_delay $in1_delay -clock $WORD_CLK_NAME [get_port TxUlpsExit]
set_input_delay $in1_delay -clock $WORD_CLK_NAME [get_port TxTriggerEsc]
set_input_delay $in1_delay -clock $WORD_CLK_NAME [get_port TxDataEsc]
set_input_delay $in1_delay -clock $WORD_CLK_NAME [get_port TxValidEsc]
set_input_delay $in1_delay -clock $WORD_CLK_NAME [get_port TurnRequest]
set_input_delay $in1_delay -clock $WORD_CLK_NAME [get_port TurnDisable]
set_input_delay $in1_delay -clock $WORD_CLK_NAME [get_port ForceRxmode]
set_input_delay $in1_delay -clock $WORD_CLK_NAME [get_port ForceTxStopmode]
set_input_delay $in1_delay -clock $WORD_CLK_NAME [get_port Enable]
set_input_delay $in2_delay -clock $TX_ESC_CLK_NAME [get_port LP_CD_A]
set_input_delay $in2_delay -clock $TX_ESC_CLK_NAME [get_port LP_CD_B]
set_input_delay $in2_delay -clock $TX_ESC_CLK_NAME [get_port LP_CD_C]
set_input_delay $in4_delay -clock $RX_ESC_CLK_NAME [get_port LpRx]
#Constrain Output Paths
set_output_delay $out1_delay -clock $WORD_CLK_NAME [get_port TxReadyHS]
set_output_delay $out1_delay -clock $WORD_CLK_NAME [get_port LpTxEn]
set_output_delay $out1_delay -clock $WORD_CLK_NAME [get_port HsTxEn]
set_output_delay $out1_delay -clock $WORD_CLK_NAME [get_port TxReadyEsc]
set_output_delay $out1_delay -clock $WORD_CLK_NAME [get_port Direction]
set_output_delay $out1_delay -clock $WORD_CLK_NAME [get_port Stopstate]
set_output_delay $out1_delay -clock $WORD_CLK_NAME [get_port ErrContentionLP0]
set_output_delay $out1_delay -clock $WORD_CLK_NAME [get_port ErrContentionLP1]
set_output_delay $out1_delay -clock $WORD_CLK_NAME [get_port UlpsActiveNot]
set_output_delay $out1_delay -clock $WORD_CLK_NAME [get_port ErrEsc]
set_output_delay $out1_delay -clock $WORD_CLK_NAME [get_port ErrSyncEsc]
set_output_delay $out1_delay -clock $WORD_CLK_NAME [get_port ErrControl]
set_output_delay $out1_delay -clock $WORD_CLK_NAME [get_port LpRxEn]
set_output_delay $out2_delay -clock $TX_ESC_CLK_NAME [get_port LpTx]
set_output_delay $out4_delay -clock $RX_ESC_CLK_NAME [get_port RxEscData]
set_output_delay $out4_delay -clock $RX_ESC_CLK_NAME [get_port RxValidEsc]
set_output_delay $out4_delay -clock $RX_ESC_CLK_NAME [get_port RxTriggerEsc]
set_output_delay $out4_delay -clock $RX_ESC_CLK_NAME [get_port RxUlpsEsc]
set_output_delay $out4_delay -clock $RX_ESC_CLK_NAME [get_port RxLpdtEsc]

####################################################################################
           #########################################################
                  #### Section 3 : Driving cells ####
           #########################################################
####################################################################################
 
set_driving_cell -library saed32lvt_ff1p16v25c -lib_cell IBUFFX4_LVT -pin Y [get_port TxDataHS]
set_driving_cell -library saed32lvt_ff1p16v25c -lib_cell IBUFFX4_LVT -pin Y [get_port TxSendSyncHS]
set_driving_cell -library saed32lvt_ff1p16v25c -lib_cell IBUFFX4_LVT -pin Y [get_port TxReqHS]
set_driving_cell -library saed32lvt_ff1p16v25c -lib_cell IBUFFX4_LVT -pin Y [get_port TxReqEsc]
set_driving_cell -library saed32lvt_ff1p16v25c -lib_cell IBUFFX4_LVT -pin Y [get_port TxLpdtEsc]
set_driving_cell -library saed32lvt_ff1p16v25c -lib_cell IBUFFX4_LVT -pin Y [get_port TxUlpsEsc]
set_driving_cell -library saed32lvt_ff1p16v25c -lib_cell IBUFFX4_LVT -pin Y [get_port TxUlpsExit]
set_driving_cell -library saed32lvt_ff1p16v25c -lib_cell IBUFFX4_LVT -pin Y [get_port TxTriggerEsc]
set_driving_cell -library saed32lvt_ff1p16v25c -lib_cell IBUFFX4_LVT -pin Y [get_port TxDataEsc]
set_driving_cell -library saed32lvt_ff1p16v25c -lib_cell IBUFFX4_LVT -pin Y [get_port TxValidEsc]
set_driving_cell -library saed32lvt_ff1p16v25c -lib_cell IBUFFX4_LVT -pin Y [get_port LpRx]
set_driving_cell -library saed32lvt_ff1p16v25c -lib_cell IBUFFX4_LVT -pin Y [get_port TurnRequest]
set_driving_cell -library saed32lvt_ff1p16v25c -lib_cell IBUFFX4_LVT -pin Y [get_port TurnDisable]
set_driving_cell -library saed32lvt_ff1p16v25c -lib_cell IBUFFX4_LVT -pin Y [get_port ForceRxmode]
set_driving_cell -library saed32lvt_ff1p16v25c -lib_cell IBUFFX4_LVT -pin Y [get_port ForceTxStopmode]
set_driving_cell -library saed32lvt_ff1p16v25c -lib_cell IBUFFX4_LVT -pin Y [get_port Enable]
set_driving_cell -library saed32lvt_ff1p16v25c -lib_cell IBUFFX4_LVT -pin Y [get_port LP_CD_A]
set_driving_cell -library saed32lvt_ff1p16v25c -lib_cell IBUFFX4_LVT -pin Y [get_port LP_CD_B]
set_driving_cell -library saed32lvt_ff1p16v25c -lib_cell IBUFFX4_LVT -pin Y [get_port LP_CD_C]


####################################################################################
           #########################################################
                  #### Section 4 : Output load ####
           #########################################################
####################################################################################
# WORD_CLK domain
set_load 15 [get_ports TxReadyHS]
set_load 15 [get_ports LpTxEn]
set_load 15 [get_ports HsTxEn]
set_load 15 [get_ports TxReadyEsc]
set_load 15 [get_ports Direction]
set_load 15 [get_ports Stopstate]
set_load 15 [get_ports ErrContentionLP0]
set_load 15 [get_ports ErrContentionLP1]
set_load 15 [get_ports UlpsActiveNot]
set_load 15 [get_ports ErrEsc]
set_load 15 [get_ports ErrSyncEsc]
set_load 15 [get_ports ErrControl]
set_load 15 [get_ports LpRxEn]
set_load 15 [get_ports LpTx]
set_load 15 [get_ports A]
set_load 15 [get_ports B]
set_load 15 [get_ports C]
set_load 15 [get_ports RxEscData]
set_load 15 [get_ports RxValidEsc]
set_load 15 [get_ports RxTriggerEsc]
set_load 15 [get_ports RxUlpsEsc]
set_load 15 [get_ports RxLpdtEsc]
##########



