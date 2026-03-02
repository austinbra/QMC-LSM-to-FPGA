# sim/tb_accum_regression.tcl

# Create clock
add_force {/tb_accum_regression/clk} {0 0ns} {1 5ns} -repeat_every 10ns

# Reset low, then release
add_force {/tb_accum_regression/rst_n} 0
run 50 ns
add_force {/tb_accum_regression/rst_n} 1

# Downstream always ready
add_force {/tb_accum_regression/ready_in} 1

# Example single sample
add_force -radix hex {/tb_accum_regression/x_in} 0000000A
add_force -radix hex {/tb_accum_regression/y_in} 00000014
add_force {/tb_accum_regression/valid_in} {1 0ns} {0 80ns}

# Run long enough for pipeline to finish
run 50 us

# Print final state for sanity
puts "beta = [get_value {/tb_accum_regression/beta}]"
puts "valid_out = [get_value {/tb_accum_regression/valid_out}]"
