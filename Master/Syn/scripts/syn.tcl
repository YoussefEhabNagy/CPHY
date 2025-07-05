
########################### Define Top Module ############################
                                                   
set top_module Master

##################### Define Working Library Directory ######################
                                                   
define_design_lib work -path ./work

############################# Formality Setup File ##########################
                                                   
set_svf $top_module.svf

################## Design Compiler Library Files #setup ######################

puts "###########################################"
puts "#      #setting Design Libraries          #"
puts "###########################################"

#Add the path of the libraries and RTL files to the search_path variable


set_app_var search_path "/home/tools/PDK/SAED32_EDK/lib/stdcell_lvt/db_ccs" 
set_app_var link_library   "* saed32lvt_ff1p16v25c.db"
set_app_var target_library "saed32lvt_ff1p16v25c.db"

set PROJECT_PATH /home/svgpdditi25mowaleed/CPHY
lappend search_path $PROJECT_PATH/RTL/sync_level
lappend search_path $PROJECT_PATH/RTL/Esc_Encoder
lappend search_path $PROJECT_PATH/RTL/mapper
lappend search_path $PROJECT_PATH/RTL/HS_Serializer
lappend search_path $PROJECT_PATH/RTL/HS_Sequencer
lappend search_path $PROJECT_PATH/RTL/Mux_3Bit
lappend search_path $PROJECT_PATH/RTL/Esc_Sequencer
lappend search_path $PROJECT_PATH/RTL/ESC_Serializer
lappend search_path $PROJECT_PATH/RTL/Mux_1Bit
lappend search_path $PROJECT_PATH/RTL/Esc_Encoder
lappend search_path $PROJECT_PATH/RTL/Encoder
lappend search_path $PROJECT_PATH/RTL/TX_Ctrl_Logic
lappend search_path $PROJECT_PATH/RTL/Esc_Decoder
lappend search_path $PROJECT_PATH/RTL/ESC_Deserializer
lappend search_path $PROJECT_PATH/RTL/Rx_Ctrl_Decoder
lappend search_path $PROJECT_PATH/RTL/TxTimer
lappend search_path $PROJECT_PATH/RTL/RxTimer
lappend search_path $PROJECT_PATH/RTL/cphy_tx_fsm
lappend search_path $PROJECT_PATH/RTL/ContentionDetection
lappend search_path $PROJECT_PATH/RTL/Clock_Recovery_LP
lappend search_path $PROJECT_PATH/RTL/Master

## Standard Cell libraries 
#set target_library "saed32hvt_dlvl_ff0p85v25c_i0p85v.db"


## Standard Cell & Hard Macros libraries 
#set link_library "saed32hvt_dlvl_ff0p85v25c_i0p85v.db" 
 

######################## Reading RTL Files #################################

puts "###########################################"
puts "#             Reading RTL Files           #"
puts "###########################################"

analyze   -format verilog /home/svgpdditi25mowaleed/CPHY/RTL/sync_level.v
read_file -format verilog /home/svgpdditi25mowaleed/CPHY/RTL/HS_Sequencer.v
read_file -format verilog /home/svgpdditi25mowaleed/CPHY/RTL/Esc_Encoder.v
read_file -format verilog /home/svgpdditi25mowaleed/CPHY/RTL/mapper.v
read_file -format verilog /home/svgpdditi25mowaleed/CPHY/RTL/HS_Serializer.v
read_file -format verilog /home/svgpdditi25mowaleed/CPHY/RTL/Mux_3Bit.v
read_file -format verilog /home/svgpdditi25mowaleed/CPHY/RTL/Esc_Sequencer.v
read_file -format verilog /home/svgpdditi25mowaleed/CPHY/RTL/ESC_Serializer.v
read_file -format verilog /home/svgpdditi25mowaleed/CPHY/RTL/Mux_1Bit.v
read_file -format verilog /home/svgpdditi25mowaleed/CPHY/RTL/Esc_Decoder.v
read_file -format verilog /home/svgpdditi25mowaleed/CPHY/RTL/Encoder.v
read_file -format verilog /home/svgpdditi25mowaleed/CPHY/RTL/TX_Ctrl_Logic.v
read_file -format verilog /home/svgpdditi25mowaleed/CPHY/RTL/Esc_Decoder.v
read_file -format verilog /home/svgpdditi25mowaleed/CPHY/RTL/ESC_Deserializer.v
read_file -format verilog /home/svgpdditi25mowaleed/CPHY/RTL/Rx_Ctrl_Decoder.v
read_file -format verilog /home/svgpdditi25mowaleed/CPHY/RTL/TX_Timer.sv
read_file -format verilog /home/svgpdditi25mowaleed/CPHY/RTL/FSM_TX.sv
read_file -format verilog /home/svgpdditi25mowaleed/CPHY/RTL/ContentionDetection.v
read_file -format verilog /home/svgpdditi25mowaleed/CPHY/RTL/RxTimer.v
read_file -format verilog /home/svgpdditi25mowaleed/CPHY/RTL/Clock_Recovery_LP.v
read_file -format verilog /home/svgpdditi25mowaleed/CPHY/RTL/Master.v

###################### Defining toplevel ###################################

current_design $top_module

#################### Liniking All The Design Parts #########################
puts "###############################################"
puts "######## Liniking All The Design Parts ########"
puts "###############################################"



link 

#################### Liniking All The Design Parts #########################
puts "###############################################"
puts "######## checking design consistency ##########"
puts "###############################################"

check_design >> reports/check_design.rpt

#################### Define Design Constraints #########################
puts "###############################################"
puts "############ Design Constraints #### ##########"
puts "###############################################"

source -echo ./cons.tcl

###################### Mapping and optimization ########################
puts "###############################################"
puts "########## Mapping & Optimization #############"
puts "###############################################"

#compile 
# Set higher effort on optimization
compile_ultra -no_autoungroup

##################### Close Formality Setup file ###########################

set_svf -off

#############################################################################
# Write out files
#############################################################################

write_file -format verilog -hierarchy -output netlists/$top_module.ddc
write_file -format verilog -hierarchy -output netlists/$top_module.v
write_sdf  sdf/$top_module.sdf
write_sdc  -nosplit sdc/$top_module.sdc

####################### reporting ##########################################

report_area -hierarchy > reports/area.rpt
report_power -hierarchy > reports/power.rpt
report_timing -delay_type min -max_paths 100 > reports/hold.rpt
report_timing -delay_type max -max_paths 100 > reports/setup.rpt
report_clock -attributes > reports/clocks.rpt
report_constraint -all_violators -nosplit > reports/constraints.rptSSS

set tns 0.0
set wns 0.0
set lps 1.0e9  ;# Large positive number to find minimum

foreach_in_collection path [get_timing_paths -max_paths 10000] {
    set slack [get_attribute $path slack]

    if {$slack < 0} {
        set tns [expr {$tns + $slack}]
        if {$slack < $wns} {
            set wns $slack
        }
    } else {
        if {$slack < $lps} {
            set lps $slack
        }
    }
}

puts "Total Negative Slack (TNS): $tns"
puts "Worst Negative Slack (WNS): $wns"
puts "Least Positive Slack: $lps"


################# starting graphical user interface #######################

#gui_start

#exit
