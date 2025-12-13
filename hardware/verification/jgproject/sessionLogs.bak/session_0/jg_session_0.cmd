# ----------------------------------------
# Jasper Version Info
# tool      : Jasper 2024.06
# platform  : Linux 4.18.0-553.89.1.el8_10.x86_64
# version   : 2024.06p002 64 bits
# build date: 2024.09.02 16:28:38 UTC
# ----------------------------------------
# started   : 2025-12-13 00:24:58 EST
# hostname  : micro16.(none)
# pid       : 1625782
# arguments : '-label' 'session_0' '-console' '//127.0.0.1:36029' '-style' 'windows' '-data' 'AAAAhnicY2RgYLCp////PwMYMD6A0Aw2jAyoAMRnQhUJbEChGRhYYZphSkAaOBh0GdIYChjKgGwhhjyGJIZ8hhSGSgY9hhKGZIYcsDoAPpsL4g==' '-proj' '/homes/user/stud/fall24/kdn2117/FormalVerification/n-body-sim/hardware/verification/jgproject/sessionLogs/session_0' '-init' '-hidden' '/homes/user/stud/fall24/kdn2117/FormalVerification/n-body-sim/hardware/verification/jgproject/.tmp/.initCmds.tcl' 'nbody.tcl'
# ----------------------------------------
#  Copyright (c) 2017 Cadence Design Systems, Inc. All Rights
#  Reserved.  Unpublished -- rights reserved under the copyright 
#  laws of the United States.
# ----------------------------------------
clear -all

set HOME_DIR ".."

# analyze -verilog
analyze -sv \
  $HOME_DIR/nbody.sv \
  $HOME_DIR/getAccl.sv \
  $HOME_DIR/shift_register.sv \
  $HOME_DIR/display.sv \
  $HOME_DIR/Mult.v \
  $HOME_DIR/InvSqrt.v \
  $HOME_DIR/AddSub.v \
  $HOME_DIR/RAM_DISP.v \
  $HOME_DIR/RAM.v \
  $HOME_DIR/RAM2.v \

set blackbox_list [list "Mult" "InvSqrt" "AddSub" "RAM_DISP" "RAM" "RAM2"]
  
# Elaborate design and properties
elaborate -top nbody -bbox_m "$blackbox_list"

# Set up Clocks and Resets
clock clk 
reset rst 

# Get design information to check general complexity
get_design_info

# Prove properties
prove -all

# Report proof results
report

