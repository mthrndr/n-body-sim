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
elaborate -top nbody -bbox_m "$blackbox_list" \
    -parameter AddTime 1 \
    -parameter MultTime 1 \
    -parameter InvSqrtTime 1 \

# Set up Clocks and Resets
clock clk 
reset rst 

# Get design information to check general complexity
get_design_info

# Prove properties
prove -all

# Report proof results
report
