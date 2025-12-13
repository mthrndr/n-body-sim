# TOP-LEVEL TEMPLATE - BEGIN
#
# QSYS_SIMDIR is used in the Quartus-generated IP simulation script to
# construct paths to the files required to simulate the IP in your Quartus
# project. By default, the IP script assumes that you are launching the
# simulator from the IP script location. If launching from another
# location, set QSYS_SIMDIR to the output directory you specified when you
# generated the IP script, relative to the directory from which you launch
# the simulator.
#
# Define the base directory for IP cores if needed, adjust path as necessary
# set IP_BASE_DIR "."

# --- Compile Quartus Libraries ---
# Set any compilation options you require (this is unusual).
# set USER_DEFINED_COMPILE_OPTIONS <compilation options>
# set USER_DEFINED_VHDL_COMPILE_OPTIONS <compilation options for VHDL>
# set USER_DEFINED_VERILOG_COMPILE_OPTIONS <compilation options for Verilog>

# Call command to compile the Quartus EDA simulation library.
echo "Compiling Quartus libraries..."
# dev_com

# --- Compile IP Cores ---
# Source and compile each IP core's simulation files

# Multiplier IP
echo "Compiling Multiplier IP (Mult_sim)..."
set QSYS_SIMDIR ../Mult_sim
source $QSYS_SIMDIR/mentor/msim_setup.tcl
com

# Adder/Subtractor IP
echo "Compiling Adder/Subtractor IP (AddSub_sim)..."
set QSYS_SIMDIR ../AddSub_sim
source $QSYS_SIMDIR/mentor/msim_setup.tcl
com

# Inverse Square Root IP
echo "Compiling Inverse Square Root IP (InvSqrt_sim)..."
set QSYS_SIMDIR ../InvSqrt_sim
source $QSYS_SIMDIR/mentor/msim_setup.tcl
com

# --- Compile Design and Testbench Files ---
# Add commands to compile all your custom design files and testbench files.
# Replace <your_design_files.v> and <your_testbench.v> with actual file names/paths.
# Add -L altera_mf_ver etc. if needed for Altera primitives not included by IP cores
echo "Compiling design and testbench files..."
vlog -sv  +incdir+./ \
     ../shift_register.sv \
     ../getAccl.sv \
     ../nbody.sv \
     ../display.sv \
     ../display_sim/RAM_DISP.v \
     ../RAM.v \
     ../RAM2.v \
     nbodyTb.sv

# Example:
# vlog +incdir+../src \
#      ../src/my_module1.v \
#      ../src/my_module2.v \
#      ../tb/top_level_tb.v

# --- Elaboration ---
# Set the top-level simulation or testbench module/entity name.
# Replace <your_top_level_tb_module> with the actual name.
echo "Elaborating design..."
# *** FIX: Use the MODULE name, not the filename ***

# Set any elaboration options you require.
# set USER_DEFINED_ELAB_OPTIONS <elaboration options>
# *** FIX: Add library linking options ***
# Add libraries for your compiled IP and standard Altera libraries.
# Check the IP core msim_setup.tcl scripts if these names are different.
# *** FIX: Add +acc for waveform logging visibility ***
set USER_DEFINED_ELAB_OPTIONS "-L altera_mf_ver -L lpm_ver -voptargs=+acc=npr -suppress 14408"
# Call command to elaborate your design and testbench.
# The -L options link libraries compiled earlier (Quartus libs, IP libs)
# Add -svlog to elab if your top-level is SystemVerilog
elab $USER_DEFINED_ELAB_OPTIONS nbodyTb

# --- Waveform Logging ---
# Add signals to the wave window and log them to the WLF file
echo "Setting up waveform logging..."
# Log all signals recursively starting from the top level
log -r /*
# Example: Log specific signals
# log clk
# log reset
# log /getAcclTb/dut_instance/internal_signal

# --- Simulation ---
# Run the simulation.
echo "Running simulation..."
run -a

# Report success to the shell.
echo "Simulation finished successfully."
#
# TOP-LEVEL TEMPLATE - END
add wave -position insertpoint  \
sim:/nbodyTb/dut/state \
sim:/nbodyTb/dut/readdata \
sim:/nbodyTb/dut/write_vy_data \
sim:/nbodyTb/dut/write_vx_data \
sim:/nbodyTb/dut/write_m_data \
sim:/nbodyTb/dut/write_x_data \
sim:/nbodyTb/dut/write_y_data \
sim:/nbodyTb/dut/m_read_addr \
sim:/nbodyTb/dut/v_read_addr \
sim:/nbodyTb/dut/pos_input_1_addr \
sim:/nbodyTb/dut/pos_input_2_addr \
sim:/nbodyTb/dut/v_write_addr
