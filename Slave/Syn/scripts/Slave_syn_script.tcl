set Top_module  slave


	# put the path and libs
	# --- Define Search path & Libraries ---- # 
	 
	#set_app_var search_path "/home/tools/PDK/SAED32_EDK/lib/stdcell_lvt/db_ccs"


	lappend search_path  "/home/tools/PDK/SAED32_EDK/lib/stdcell_lvt/db_ccs"


	set_app_var target_library     "saed32lvt_ff1p16v25c.db"  	
	set_app_var link_library "* $target_library"

	# --- Remove any work --- #
	# Repitive operations 
	sh rm -rf work
	sh mkdir -p work

	# For define enviroment files for reduced run time of tools to store intermideate files 
	define_design_lib work -path ./work




	# read all files and the top must be  the last file
	#analyze -format verilog ../rtl/Clock_Gating.v
	analyze -format verilog ../rtl/Clock_Recovery_LP.v
	analyze -format verilog ../rtl/ContentionDetection.v
	analyze -format sverilog ../rtl/Decoder.sv
	analyze -format verilog ../rtl/demapper.v
	analyze -format verilog ../rtl/Esc_Decoder.v
	analyze -format verilog ../rtl/ESC_Deserializer.v
	analyze -format verilog ../rtl/Esc_Encoder.v
	analyze -format sverilog ../rtl/Esc_Sequencer.sv
	analyze -format verilog ../rtl/ESC_Serializer.v
	analyze -format verilog ../rtl/HS_Deserializer.v
	analyze -format verilog ../rtl/Mux_1Bit.v
	analyze -format verilog ../rtl/Rx_Ctrl_Decoder.v
	analyze -format verilog ../rtl/RxTimer.v
	#read_file -format verilog ../rtl/reg_file.v
	analyze   -format verilog ../rtl/reg_file.v
	analyze -format verilog ../rtl/Sequence_Detector.v
	analyze -format sverilog ../rtl/SlaveFSM.sv
	#read_file -format verilog ../rtl/synchronizer.v
	analyze   -format verilog ../rtl/synchronizer.v
	analyze -format verilog ../rtl/TX_Ctrl_Logic.v
	analyze -format verilog ../rtl/TxTimer.v
	analyze -format verilog ../rtl/Word_Clock_Gen.v
	analyze -format verilog ../rtl/Slave.v
	elaborate slave


	# - Return name of current design  
	current_design slave

	# - locate all of the designs and library components referenced in the current design and connect them to the current design.
	link 
	# - Checks for detects any errors in design 
	check_design >> ../reports/check_design.rpt

	# -- Apply Constraints on Design 
	source -echo ../cons/Slave_cons.tcl


	group_path -name INOUT -from [all_inputs] -to [all_outputs]
	# -- to remove assign statement
	set verilogout_no_tri	 true
	set verilogout_equation  false
	set_fix_multiple_port_nets -all -buffer_constants 




	# -- Optimize and mapping 
	#compile -map_effort high	
	compile_ultra -retime

	#--- check design post compile
	check_design >> ../reports/check_design_post_compile.rpt

	#--- change names
	define_name_rules no_case -case_insensitive
	change_names -rule no_case -hierarchy
	change_names -rule verilog -hierarchy

	# Save Results output 
	write_file -format verilog -hierarchy -output ../synout/Slave_Netlist.v

	# DDC Gate Level Netlist
	write_file -format ddc -hierarchy -output ../synout/Slave.ddc
	# SDC(Synopsys Design Constraints) File
	write_sdc -nosplit ../synout/Slave.sdc
	# SDF(Standard Delay Format) File
	write_sdf ../synout/Slave.sdf

	# reports
	report_area -hierarchy > ../reports/area.rpt
	report_power -hierarchy > ../reports/power.rpt
	report_timing -max_paths 10 -delay_type min > ../reports/hold.rpt
	report_timing -max_paths 10 -delay_type max > ../reports/setup.rpt
	report_constraint -all_violators > ../reports/constraints.rpt
	report_qor > ../reports/qor.rpt

	# Open the input file for reading
	set in_file [open "syn.log" r]

	# Open the output file for writing
	set out_file [open "warning.txt" w]

	# Read lines one by one
	while {[gets $in_file line] >= 0} {
	    if {[string match -nocase *warn* $line]} {
		puts $out_file $line
	    }
	}
	while {[gets $in_file line] >= 0} {
	    if {[string match -nocase *error* $line]} {
		puts $out_file $line
	    }
	}

	# Close the files
	close $in_file
	close $out_file


	#gui_start
	exit
