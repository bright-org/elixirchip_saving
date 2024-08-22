
# 775MHz (BUFG/DSPの限界)
#create_clock -period 1.291 -name clk -waveform {0.000 0.6455} [get_ports clk]

# 738MHz (BRAMの限界)
create_clock -period 1.356 -name clk -waveform {0.000 0.6780} [get_ports clk]

# 666MHz
# create_clock -period 1.500 -name clk -waveform {0.000 0.8335} [get_ports clk]

# 600MHz (URAMの限界)
#create_clock -period 1.667 -name clk -waveform {0.000 0.7500} [get_ports clk]

# 500MHz
# create_clock -period 2.000 -name clk -waveform {0.000 1.000} [get_ports clk]


#set_property IOSTANDARD LVCMOS12 [get_ports reset]
#set_property IOSTANDARD LVCMOS12 [get_ports clk]
#set_property IOSTANDARD LVCMOS12 [get_ports cke]
#set_property IOSTANDARD LVCMOS12 [get_ports {din[*]}]
#set_property IOSTANDARD LVCMOS12 [get_ports {dout[*]}]

#set_property PACKAGE_PIN AA11 [get_ports reset]
#set_property PACKAGE_PIN AB11 [get_ports clk]
#set_property PACKAGE_PIN AA10 [get_ports {din[*]}]
#set_property PACKAGE_PIN AC11 [get_ports {dout[*]}]

#set_property IOSTANDARD LVCMOS12 [get_ports reset]
#set_property IOSTANDARD LVCMOS12 [get_ports clk]
#set_property IOSTANDARD LVCMOS12 [get_ports {din[*]}]
#set_property IOSTANDARD LVCMOS12 [get_ports {dout[*]}]
