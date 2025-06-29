set_property PACKAGE_PIN W5 [get_ports clk_100]   # on Arty A7
create_clock -period 10.0 [get_ports clk_100]     # 100 MHz
set_property PACKAGE_PIN G13 [get_ports uart_rxd]
set_property PACKAGE_PIN G14 [get_ports uart_txd]
# …any other pin assignments…
