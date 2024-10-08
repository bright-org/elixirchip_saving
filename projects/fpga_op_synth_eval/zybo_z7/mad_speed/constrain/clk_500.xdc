

# create_clock -period 1.0 -name clk -waveform {0.000 0.5000} [get_ports clk]

# 725MHz
# create_clock -period 1.380 -name clk -waveform {0.000 0.690} [get_ports clk]

# 650MHz
# create_clock -period 1.538 -name clk -waveform {0.000 0.769} [get_ports clk]

# 645MHz
# create_clock -period 1.550 -name clk -waveform {0.000 0.775} [get_ports clk]

# 644MHz
# create_clock -period 1.553 -name clk -waveform {0.000 0.7765} [get_ports clk]

# 605MHz
# create_clock -period 1.652 -name clk -waveform {0.000 0.8264} [get_ports clk]

# 600MHz
# create_clock -period 1.6667 -name clk -waveform {0.000 0.8333} [get_ports clk]

# 550MHz
# create_clock -period 1.818 -name clk -waveform {0.000 0.909} [get_ports clk]

# 520MHz
# create_clock -period 1.923 -name clk -waveform {0.000 0.9615} [get_ports clk]

# 500MHz
create_clock -period 2.000 -name clk -waveform {0.000 1.000} [get_ports clk]
