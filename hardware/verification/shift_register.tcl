# ----------------------------------------
#  Copyright (c) 2017 Cadence Design Systems, Inc. All Rights
#  Reserved.  Unpublished -- rights reserved under the copyright 
#  laws of the United States.
# ----------------------------------------
clear -all

set HOME_DIR "."

# analyze -verilog
analyze -sv \
  $HOME_DIR/shift_register.sv \
\


elaborate -top shift_register
# Set up Clocks and Resets
clock clk 
reset rst 


# Get design information to check general complexity
get_design_info

# Prove properties
prove -all

# Report proof results
report
