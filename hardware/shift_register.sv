module shift_register #(
    parameter SHIFTS = 4 // Number of shifts (delay cycles)
)(
    input wire clk,                  // Clock signal
    input wire rst,                  // Reset signal (active high)
    input wire [63:0] in,            // 64-bit input signal
    output wire [63:0] out           // 64-bit output signal
);

    // Internal shift register storage
    reg [63:0] shift_reg [SHIFTS-1:0];

    // Shift register logic
    always @(posedge clk or posedge rst) begin
        if (rst) begin
            integer i;
            for (i = 0; i < SHIFTS; i = i + 1) begin
                shift_reg[i] <= 64'b0; // Reset all bits to 0
            end
        end else begin
            integer i;
            for (i = SHIFTS-1; i > 0; i = i - 1) begin
                shift_reg[i] <= shift_reg[i-1]; // Shift values
            end
            shift_reg[0] <= in; // Insert new input
        end
    end

    // Output the value from SHIFTS cycles ago
    assign out = shift_reg[SHIFTS-1];



   // 1) Reset clears output 
    a_reset_clears_out:
    assert property (@(posedge clk or posedge rst)
        rst |=> (out == 64'b0)
    );

    // 2) Stage0 loads previous input each cycle (when not in reset)
    a_stage0_loads_in:
    assert property (@(posedge clk) disable iff (rst)
        (!rst && !$past(rst)) |-> (shift_reg[0] == $past(in))
    );

    // 3) Each stage shifts from previous stage (when not in reset)
    genvar gi;
    generate
      for (gi = 1; gi < SHIFTS; gi = gi + 1) begin : gen_shift_chain
        a_stage_shifts:
        assert property (@(posedge clk) disable iff (rst)
            $past(1'b1) |-> (shift_reg[gi] == $past(shift_reg[gi-1]))
        );
      end
    endgenerate

    // 4) End-to-end delay contract: out == in delayed by SHIFTS cycles
    a_delay_correct:
    assert property (@(posedge clk) disable iff (rst)
        (!rst && !$past(rst, SHIFTS)) |-> (out == $past(in, SHIFTS))
    );

    // 5) Cover: see some activity propagate through the delay
    c_in_changes_then_out_changes:
    cover property (@(posedge clk) disable iff (rst)
        $changed(in) ##SHIFTS $changed(out)
    );

endmodule

/*
Issue 1: Module was automatically black-boxed

Problem:
The shift register contains a large register array. Jasper automatically black-boxed the module to avoid state-space explosion. As a result, internal registers and assertions were not actually checked.

Solution:
The shift register was verified in isolation, allowing the tool to fully elaborate the internal registers. At the system level, the shift register is treated as a black-box delay element with an assumed delay contract.

Issue 2: Assertions failed due to asynchronous reset behavior
Problem:
The shift register uses an asynchronous reset. Original assertions using $past(...) did not account for reset boundaries. When reset asserted, registers were cleared to zero while $past(in) still referred to pre-reset values, causing valid assertion failures.

Solution:
Assertions were rewritten to be reset-aware, checking behavior only when both the current and previous cycles were not in reset.
*/



