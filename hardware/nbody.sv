// This module is the wrapper for the entire system. It will take in values from the bus
// write to its memories, and call getaccl and leapfrog
//
// Lower 9 (log2 BODIES) bits are body number
// Upper 7 (16 - log2 BODIES) bits other params
// REGISTERS:
// 0000000 = GO
// 0000001 = READ
// 0000010 = N_BODIES
// 0000011 = GAP
// MEMORY:
// 0000100 = write_x_data_LOWER
// 0000101 = write_x_data_UPPER
// 0000110 = write_y_data_LOWER
// 0000111 = write_y_data_UPPER
// 0001000 = write_m_data_LOWER
// 0001001 = write_m_data_UPPER
// 0001010 = write_vx_data_LOWER
// 0001011 = write_vx_data_UPPER
// 0001100 = write_vy_data_LOWER
// 0001101 = write_vy_data_UPPER

// 1000000 = DONE
// 1000001 = READ_X_LOWER
// 1000010 = READ_X_UPPER
// 1000011 = READ_Y_LOWER
// 1000100 = READ_Y_UPPER


`timescale 1 ps / 1 ps
module nbody #(
    parameter BODIES = 512,
    parameter EXT_DATA_WIDTH = 32, // for Reading and writing from the bus :)
    parameter DATA_WIDTH = 64,
    parameter ADDR_WIDTH = 16,
    parameter BODY_ADDR_WIDTH = $clog2(BODIES),
    parameter MultTime = 5, // Number of cycles for mult
    parameter AddTime = 9, // Number of cycles for add/sub 
    parameter InvSqrtTime = 17, // Number of cycles for invsqert
    parameter AcclLatency = AddTime + MultTime + AddTime + InvSqrtTime + MultTime * 4 + 1, // The one is for the startup thing we need to do to confirm we dont devide by 0
    parameter MinBodies = 21
)(
    input logic clk,
    input logic rst,
    input logic [EXT_DATA_WIDTH-1:0] writedata,
    input logic read,
    input logic write,
    input logic [ADDR_WIDTH-1:0] addr,
    input logic chipselect,
    output logic [EXT_DATA_WIDTH-1:0] readdata,
    output logic [7:0] VGA_R, VGA_G, VGA_B,
	output logic 	   VGA_CLK, VGA_HS, VGA_VS,
		                   VGA_BLANK_n,
	output logic 	   VGA_SYNC_n

);

    localparam SW_READ_WRITE = 2'b00;
    localparam CALC_ACCEL = 2'b01;
    localparam UPDATE_POS = 2'b10;

    // Registers:
    localparam GO             = 7'h40;
    localparam READ           = 7'h41;
    localparam N_BODIES       = 7'h42;
    localparam GAP            = 7'h43;
    // Memory:
    localparam X_SEL_LOWER    = 7'h44;
    localparam X_SEL_UPPER    = 7'h45;
    localparam Y_SEL_LOWER    = 7'h46;
    localparam Y_SEL_UPPER    = 7'h47;
    localparam M_SEL_LOWER    = 7'h48;
    localparam M_SEL_UPPER    = 7'h49;
    localparam VX_SEL_LOWER   = 7'h4a;
    localparam VX_SEL_UPPER   = 7'h4b;
    localparam VY_SEL_LOWER   = 7'h4c;
    localparam VY_SEL_UPPER   = 7'h4d;
    // Out:
    localparam DONE           = 7'h50;
    localparam READ_X_LOWER   = 7'h51;
    localparam READ_X_UPPER   = 7'h52;
    localparam READ_Y_LOWER   = 7'h53;
    localparam READ_Y_UPPER   = 7'h54;

    logic go;
    logic done;
    logic read_sw;
    logic [$clog2(BODIES)-1:0] num_bodies;
    logic [EXT_DATA_WIDTH-1:0] gap, gap_counter;
    logic [DATA_WIDTH-1:0] write_vy_data, write_vx_data, write_m_data, write_x_data, write_y_data;
    logic wren_x, wren_y, wren_m, wren_vx, wren_vy;
    logic [DATA_WIDTH-1:0] out_x, out_y, out_m, out_vx, out_vy;
    logic [1:0] state;
    logic [BODY_ADDR_WIDTH-1:0] m_read_addr, v_read_addr;
    logic [BODY_ADDR_WIDTH-1:0] pos_input_1_addr;
    logic [BODY_ADDR_WIDTH-1:0] pos_input_2_addr;
    logic [BODY_ADDR_WIDTH-1:0] s1_counter;
    
    logic [DATA_WIDTH-1:0] ax, ay;
    logic [DATA_WIDTH-1:0] ax_shifted, ay_shifted;

    logic [BODY_ADDR_WIDTH-1:0] p_read_i, p_read_j, v_read_i, v_read_j, v_write_i, v_write_j;
    logic valid_accl, valid_dv;

    logic [DATA_WIDTH-1:0] x_output_1, y_output_1, x_output_2, y_output_2; 
    // Odd things will happen if you try to write when the hardware is not in a state where it expects you too, as the addresses passed into the ram will be wrong, but you will still be writing.
    logic state_2_write_enable; // This one is 0 when when we are not in state 2, if if we are, it tracks whether we are writing (based on latency of adders and such)
    logic [BODY_ADDR_WIDTH-1:0] v_write_addr;
    
    logic [BODY_ADDR_WIDTH-1:0] state_2_read, state_2_pos_write;

    logic [DATA_WIDTH-1:0] add_x_out, add_y_out, add_x_input_1, add_x_input_2, add_y_input_1, add_y_input_2;
    logic [EXT_DATA_WIDTH-1:0] write_register;
    logic [31:0] state_1_timer;
    logic endstate;

    logic first_time;


    // Instantiating the display
    Display display(
        .clk(clk),
        .reset(rst),
        .writedata(writedata),
        .write(write&(~addr[15])), // Don't write to the display
        .chipselect(chipselect),
        .address(addr[14:0]),
        .VGA_R(VGA_R), 
        .VGA_G(VGA_G), 
        .VGA_B(VGA_B),
        .VGA_CLK(VGA_CLK), 
        .VGA_HS(VGA_HS), 
        .VGA_VS(VGA_VS),
        .VGA_BLANK_n(VGA_BLANK_n),
        .VGA_SYNC_n(VGA_SYNC_n)
    ); 
    // For testing: force all VGA outputs low
    

    // The main state machine
    always_ff @(posedge clk or posedge rst) begin
        //TODO: logic for letting software read and write values goes here
        if (rst) begin
            state <= SW_READ_WRITE;
            gap_counter <= 0;
            gap <= 0;
            num_bodies <= 0;
            done <= 0;
        end else begin
            if (write == 1 && chipselect == 1) begin
                if (addr[15:9] == GO) begin
                    go <= writedata[0];
                end else if (addr[15:9] == READ) begin
                    read_sw <= writedata[0];
                end else if (addr[15:9] == N_BODIES) begin
                    num_bodies <= writedata[BODY_ADDR_WIDTH-1:0];
                end else if (addr[15:9] == GAP) begin
                    gap <= writedata;
                end
                if (addr[9] == 0) begin
                    write_register <= writedata;
                end
            end

            case (state)
                SW_READ_WRITE: begin // Software reading/writing 
                    // if go is not high, then we are not going to do anything (except take in writes from software)
                    // if we raised done, we are waiting for read to go high before dropping done
                    // once read and done are both low (and go is high obvisously), we can start the next cycle

                    if(go == 1) begin //handshake logic
                        if(read_sw == 1) begin
                            done <= 0;
                        end else if (done == 0) begin
                            state <= CALC_ACCEL;
                            state_1_timer <= 0;
                            v_write_i <= 0;
                            v_write_j <= 0;
                            v_read_i  <= 0;
                            v_read_j  <= 0;
                            p_read_i  <= 0;
                            p_read_j  <= 0;
                            valid_dv  <= 0;
                            valid_dv  <= 0;
                            valid_accl <= 0;
                            gap_counter <= 0;
                        end
                    end
                    else begin
                        first_time <= 1;
                        done <= 0;
                    end

                end
                CALC_ACCEL: begin // Compute accelerations, update velocities
                    if (go == 1'b0) begin
                        state <= SW_READ_WRITE;
                    end
                    else if (v_write_i == num_bodies - 1 && v_write_j == num_bodies - 1) begin
                        // Finished, start UPDATE_POS
                        state <= UPDATE_POS;
                        state_2_write_enable <= 1'b0;
                        state_2_pos_write <= 0;
                        state_2_read <= 0;
                        state_2_pos_write <= 0;
                        state_2_write_enable <= 1'b0;
                        state_1_timer <= 0;
                        v_write_i <= 0;
                        v_write_j <= 0;
                        v_read_i  <= 0;
                        v_read_j  <= 0;
                        p_read_i  <= 0;
                        p_read_j  <= 0;
                        valid_dv  <= 0;
                        valid_accl  <= 0;
                    end
                    else begin

                        // Increment state timer and the body we are comparing
                        // to
                        state_1_timer <= state_1_timer + 1;
                        p_read_j <= p_read_j + 9'b1;

                        // Once we have compared to every body, increment the
                        // current body being considered, and reset the counter
                        // for the bodies we compare to
                        if (p_read_j == num_bodies - 1) begin
                            p_read_j <= 9'b0;
                            p_read_i <= p_read_i + 9'b1;
                        end

                        // Once state_1_timer is equal to acclLatency - 1,
                        // valid accelerations have begun streaming out
                        if (state_1_timer == AcclLatency - 1) begin
                            valid_accl <= 1'b1;
                        end

                        // Increment counter to read in new
                        if (valid_accl) begin
                            v_read_j <= v_read_j + 9'b1;
                        end

                        // Loop over
                        if (v_read_j == num_bodies - 1) begin
                            v_read_j <= 0;
                            // Check if we can remove v_read_i
                            v_read_i <= v_read_i + 9'b1;
                        end

                        // Once state_1_timer is equal to the accl and add
                        // latency + 1, valid dv data has begun streaming out
                        if (state_1_timer == AcclLatency + AddTime + 1) begin
                            valid_dv <= 1'b1;
                        end

                        // Once we are receiving dv begin looping on v
                        if (valid_dv) begin
                            v_write_j <= v_write_j + 9'b1;
                        end

                        // Loop over
                        if (v_write_j == num_bodies - 1) begin
                            v_write_j <= 0;
                            v_write_i <= v_write_i + 9'b1;
                        end 
                        

                        
                    end
                    
                end
                UPDATE_POS: begin // Update positions

                    // Increment
                    state_2_read <= state_2_read + 9'b1;

                    if (go == 0) begin
                        state <= SW_READ_WRITE;
                    end
                    // Data has begun streaming out of adder
                    if (state_2_read == AddTime + 1) begin
                        // finished the startup time, now we can start writing things back
                        state_2_write_enable <= 1'b1;
                    end else if (state_2_write_enable) begin
                        if (state_2_pos_write != num_bodies - 1) begin
                            state_2_pos_write <= state_2_pos_write + 9'b1; // must be zeroed out at the start
                        // Finished updating positions for all bodies
                        end else begin
                            state_2_write_enable <= 1'b0;
                            state_2_pos_write <= 0;
                            first_time <= 0;
                            // We've calculated all the timesteps required, go
                            // back to SW_READ_WRITE
                            if (gap_counter == gap - 1) begin
                                state <= SW_READ_WRITE;
                                done <= 1;
                            // Not all timesteps computed, go back to
                            // CALC_ACCEL and start again
                            end else begin
                                state <= CALC_ACCEL;
                                gap_counter <= gap_counter + 1;
                            end
                        end
                    end
                end
                default: state <= SW_READ_WRITE; // Default to idle state
            endcase
        end
    end

    always_comb begin : blockName
        if (read == 1 && chipselect == 1) begin
            if (addr[15:9] == DONE) begin
                readdata = {{(EXT_DATA_WIDTH-1){1'b0}}, done};
            end else if (addr[15:9] == READ_X_LOWER) begin
                readdata =  x_output_1[EXT_DATA_WIDTH-1:0];
            end else if (addr[15:9] == READ_X_UPPER) begin
                readdata =  x_output_1[DATA_WIDTH-1:EXT_DATA_WIDTH];
            end else if (addr[15:9] == READ_Y_LOWER) begin
                readdata =  y_output_1[EXT_DATA_WIDTH-1:0];
            end else if (addr[15:9] == READ_Y_UPPER) begin
                readdata =  y_output_1[DATA_WIDTH-1:EXT_DATA_WIDTH];
            end else begin 
                readdata = {EXT_DATA_WIDTH{1'b1}};
            end
        end
        else begin
            readdata <= {EXT_DATA_WIDTH{1'b0}};
        end
        case (state)
            SW_READ_WRITE: begin
                // All the memories get the addr.
                pos_input_1_addr = addr[BODY_ADDR_WIDTH-1:0];
                pos_input_2_addr = addr[BODY_ADDR_WIDTH-1:0];
                m_read_addr = addr[BODY_ADDR_WIDTH-1:0];
                v_read_addr = addr[BODY_ADDR_WIDTH-1:0];
                v_write_addr = addr[BODY_ADDR_WIDTH-1:0];

                write_x_data = {writedata,write_register};
                write_y_data = {writedata,write_register};
                write_m_data = {writedata,write_register};
                write_vx_data = {writedata,write_register};
                write_vy_data = {writedata,write_register};

                // Write enable for the different memories
                wren_x = (addr[15:9] == X_SEL_UPPER) ? (write & chipselect) : 1'b0;
                wren_y = (addr[15:9] == Y_SEL_UPPER) ? (write & chipselect) : 1'b0;
                wren_m = (addr[15:9] == M_SEL_UPPER) ? (write & chipselect) : 1'b0;
                wren_vx = (addr[15:9] == VX_SEL_UPPER) ? (write & chipselect) : 1'b0;
                wren_vy = (addr[15:9] == VY_SEL_UPPER) ? (write & chipselect) : 1'b0;
                    
                ax_shifted = 0;
                ay_shifted = 0;
                add_x_input_1 = 0;
                add_x_input_2 = 0;
                add_y_input_1 = 0;
                add_y_input_2 = 0;

            end
            CALC_ACCEL: begin

                pos_input_1_addr = p_read_i;
                pos_input_2_addr = p_read_j;
                m_read_addr = p_read_i;
                v_read_addr = v_read_j;
                v_write_addr = v_write_j;

                // The 0 values don't matter
                write_x_data = 0;
                write_y_data = 0;
                write_m_data = 0;
                write_vx_data = add_x_out;
                write_vy_data = add_y_out;

                wren_x = 0;
                wren_y = 0;
                wren_m = 0;
                wren_vx = valid_dv;
                wren_vy = valid_dv;

                // TO DO: We are assuming big indian, if not, deal with it
                // On the first timestep we only calculate a half timestep,
                // shift to do so. Floating point shifting
                if (first_time) begin
                    ax_shifted = {ax[63], ax[62:52] > 0? ax[62:52] - 11'b1 : 11'b0, ax[51:0]};
                    ay_shifted = {ay[63], ay[62:52] > 0? ay[62:52] - 11'b1 : 11'b0, ay[51:0]};
                end else begin
                    ax_shifted = ax;
                    ay_shifted = ay;
                end

                add_x_input_1 = ax_shifted;
                add_x_input_2 = out_vx;
                add_y_input_1 = ay_shifted;
                add_y_input_2 = out_vy;


            end
            UPDATE_POS: begin
                pos_input_1_addr = state_2_pos_write; 
                pos_input_2_addr = state_2_read;
                v_read_addr = state_2_read; //also zero at the start, these should always hold the same value (v_read and pos)
                m_read_addr = 0;
                v_write_addr = 0;

                write_x_data = add_x_out; //Make sure this is zeroed out before hand
                write_y_data = add_y_out;
                write_m_data = 0;
                write_vx_data = 0;
                write_vy_data = 0;

                
                wren_x = state_2_write_enable;
                wren_y = state_2_write_enable;
                wren_m = 0;
                wren_vx = 0;
                wren_vy = 0;

                ax_shifted = 0;
                ay_shifted = 0;

                add_x_input_1 = x_output_2;
                add_x_input_2 = out_vx;
                add_y_input_1 = y_output_2;
                add_y_input_2 = out_vy;
            end
            default: begin
                // No action
            end
        endcase
    end
    // Write enable for software

    AddSub AddX(
        .clk(clk),
        .areset(rst),
        .a(add_x_input_1),
        .b(add_x_input_2),
        .q(add_x_out)
    );
    AddSub AddY(
        .clk(clk),
        .areset(rst),
        .a(add_y_input_1),
        .b(add_y_input_2),
        .q(add_y_out)
    );
    RAM2	x(
        .clock ( clk ),
        .address_a ( pos_input_1_addr ),
        .address_b ( pos_input_2_addr ),
        .data_a ( write_x_data ),
        .data_b ( 64'b0 ),
        .wren_a ( wren_x ),
        .wren_b ( 1'b0 ),
        .q_a ( x_output_1 ),
        .q_b ( x_output_2 )
	);
    RAM2    y(
        .clock ( clk ),
        .address_a ( pos_input_1_addr ),
        .address_b ( pos_input_2_addr ),
        .data_a ( write_y_data ),
        .data_b ( 64'b0 ),
        .wren_a ( wren_y ),
        .wren_b ( 1'b0 ),
        .q_a ( y_output_1 ),
        .q_b ( y_output_2 )
	);
    RAM	RAM_m (
        .clock ( clk ),
        .data ( write_m_data ),
        .rdaddress ( m_read_addr ),
        .wraddress ( addr[BODY_ADDR_WIDTH-1:0] ),
        .wren ( wren_m ),
        .q ( out_m )
	);
    RAM	RAM_vx (
        .clock ( clk ),
        .data ( write_vx_data ),
        .rdaddress ( v_read_addr ),
        .wraddress ( v_write_addr ),
        .wren ( wren_vx ),
        .q ( out_vx )
	);
    RAM	RAM_vy (
        .clock ( clk ),
        .data ( write_vy_data ),
        .rdaddress ( v_read_addr ),
        .wraddress ( v_write_addr ),
        .wren ( wren_vy ),
        .q ( out_vy )
	);
    
    getAccl #(
        .MultTime(MultTime),
        .AddTime(AddTime),
        .InvSqrtTime(InvSqrtTime)
    ) accl (
        .rst(rst), // NOT CORRECT TODO
        .clk(clk),
        .x1(x_output_1),
        .y1(y_output_1),
        .x2(x_output_2),
        .y2(y_output_2),
        .m2(out_m),
        .ax(ax),
        .ay(ay)
    );

/*
// Assertion
property done_must_be_in_state_rw();
    @(posedge clk) (done |-> (state == SW_READ_WRITE));
endproperty

a_done_must_be_in_state_rw: assert property (done_must_be_in_state_rw);

// ============================================================
// Assumptions for FSM transition verification (non-overconstraining)
// ============================================================

// Flag for configuration done:
logic seen_nb, seen_gap;
always_ff @(posedge clk or posedge rst) begin
  if (rst) begin
    seen_nb  <= 1'b0;
    seen_gap <= 1'b0;
  end else begin
    if (chipselect && write && (addr[15:9] == N_BODIES)) seen_nb  <= 1'b1;
    if (chipselect && write && (addr[15:9] == GAP))      seen_gap <= 1'b1;
  end
end

wire cfg_done = seen_nb && seen_gap;


// 2) Write should only happens under the stage SW_READ_WRITE
// as_write_inRW:
// assume property (@(posedge clk) disable iff (rst)
//   chipselect && write |-> state == SW_READ_WRITE
// );

as_write_only_inRW_except_GO:
assume property (@(posedge clk) disable iff (rst)
  (chipselect && write && (addr[15:9] != GO)) |-> (state == SW_READ_WRITE)
);


// 3) Write should only happens under the stage SW_READ_WRITE
as_go_only_after_cfg:
assume property (@(posedge clk) disable iff (rst)
  go |-> cfg_done
);


// 4) Write should only happens under the stage SW_READ_WRITE
as_cfg_values_legal:
assume property (@(posedge clk) disable iff (rst)
  cfg_done |-> (num_bodies >= 1 && num_bodies <= 10 && gap > 0)
);


// 5) configuration parameters num_bodies and gap remain unchanged while the accelerator is running
as_cfg_stable_while_running:
assume property (@(posedge clk) disable iff (rst)
  (state != SW_READ_WRITE) |-> ($stable(num_bodies) && $stable(gap))
);


// 6) Whenever the hardware asserts done, the software will eventually issue a read request (read_sw) within 1 to 500 clock cycles.
as_read_eventually_after_done:
assume property (@(posedge clk) disable iff (rst)
  done |-> ##[1:500] read_sw
);


// 7) Read is set high only in the stage SW_READ_WRITE
as_read_only_inRW:
assume property (@(posedge clk) disable iff (rst)
  read_sw |-> state == SW_READ_WRITE
);
///////////////////////////////////////////////////



//cover every stages
cover_SW_READ_WRITE:
cover property (@(posedge clk) disable iff (rst)
  state == SW_READ_WRITE
);

cover_CALC_ACCEL:
cover property (@(posedge clk) disable iff (rst)
  state == CALC_ACCEL
);

cover_UPDATE_POS:
cover property (@(posedge clk) disable iff (rst)
  state == UPDATE_POS
);


//configuration done (same as before)
logic seen_nb, seen_gap;
always_ff @(posedge clk or posedge rst) begin
  if (rst) begin
    seen_nb  <= 1'b0;
    seen_gap <= 1'b0;
  end else begin
    if (chipselect && write && (addr[15:9] == N_BODIES)) seen_nb  <= 1'b1;
    if (chipselect && write && (addr[15:9] == GAP))      seen_gap <= 1'b1;
  end
end
wire cfg_done = seen_nb && seen_gap;

// transition: from SW_READ_WRTIE to CALC_ACCEL(check cfg_done go read_sw done)
ap_rw_to_calc:
assert property (@(posedge clk) disable iff (rst)
  (state==SW_READ_WRITE && cfg_done && go && !read_sw && !done)
  |=> (state==CALC_ACCEL)
);

// transition: SW_READ_WRTIE stays (check cfg_done go read_sw done)
ap_rw_stays_rw_when_not_start:
assert property (@(posedge clk) disable iff (rst)
  (state==SW_READ_WRITE && (!go || read_sw || done || !cfg_done))
  |=> (state==SW_READ_WRITE) 
);

// transition: from CALC to RW on !go 
ap_calc_abort:
assert property (@(posedge clk) disable iff (rst)
  (state==CALC_ACCEL && !go)
  |=> (state==SW_READ_WRITE)
);

// transition: from CALC to UPDATE when finished
ap_calc_to_update:
assert property (@(posedge clk) disable iff (rst)
  (state==CALC_ACCEL && go &&
   (v_write_i == num_bodies-1) && (v_write_j == num_bodies-1))
  |=> (state==UPDATE_POS)
);

// transition: CALC stays CALC when the calculation hasn't done
ap_calc_stays_calc_when_not_done:
assert property (@(posedge clk) disable iff (rst)
  (state==CALC_ACCEL && go &&
   !((v_write_i == num_bodies-1) && (v_write_j == num_bodies-1)))
  |=> (state==CALC_ACCEL || state==SW_READ_WRITE)
);

// transition: UPDATE to RW on !go
ap_update_abort:
assert property (@(posedge clk) disable iff (rst)
  (state==UPDATE_POS && !go)
   |=> (state==SW_READ_WRITE)
);

// In the UPDATE_POS state, the state register is assigned multiple times in the same clock cycle using non-blocking assignments. When go goes low, the RTL sets state to SW_READ_WRITE, but later logic in the same always_ff block overwrites this value (for example, setting state to CALC_ACCEL).

// Because the last assignment wins, the FSM does not return to SW_READ_WRITE even though go is low. The assertion correctly detects this missing transition.

// UPDATE finish branches
ap_update_finish_to_rw_done:
assert property (@(posedge clk) disable iff (rst)
  (state==UPDATE_POS && state_2_write_enable &&
   (state_2_pos_write == num_bodies-1) &&
   (gap_counter == gap-1))
  |=> (state==SW_READ_WRITE && done)
);


// UPDATE stays UPDATE otherwise goes to SW if !go 
ap_update_stays_update_when_not_finished:
assert property (@(posedge clk) disable iff (rst)
  (state==UPDATE_POS && go &&
   !(state_2_write_enable && (state_2_pos_write == num_bodies-1)))
  |=> (state==UPDATE_POS || state==SW_READ_WRITE) 
);


ap_state_legal: 
assert property (@(posedge clk) disable iff (rst)
  (state == SW_READ_WRITE) || (state == CALC_ACCEL) || (state == UPDATE_POS)
);

ap_p_read_in_range: assert property (@(posedge clk) disable iff (rst)
  (state == CALC_ACCEL) |-> (p_read_i <=num_bodies) && (p_read_j <=num_bodies)
);

ap_v_read_in_range: assert property (@(posedge clk) disable iff (rst)
  (state == CALC_ACCEL) |-> (v_read_i <=num_bodies) && (v_read_j <= num_bodies)
);

ap_v_write_in_range: assert property (@(posedge clk) disable iff (rst)
  (state == CALC_ACCEL) |-> (v_write_i <=num_bodies) && (v_write_j <= num_bodies)
);
*/
/*The assertions ap_p_read_in_range and ap_v_read_in_range fail due to an off-by-one counter overflow in the CALC_ACCEL state.
When both index counters reach num_bodies − 1, the inner counter resets to zero and the outer counter is incremented without an upper-bound check. As a result, the outer counter temporarily becomes equal to num_bodies, which is outside the valid range [0, num_bodies − 1] for one cycle.

Formal verification explores this boundary case and detects the out-of-range value, even though the FSM transitions shortly afterward. Simulation may not expose this issue, but formal analysis correctly flags the illegal intermediate state.*/



endmodule
