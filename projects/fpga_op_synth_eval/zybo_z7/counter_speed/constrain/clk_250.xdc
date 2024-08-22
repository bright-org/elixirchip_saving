# 464MHz (BUFGの限界)
# create_clock -period 2.155 -name clk -waveform {0.000 1.0775} [get_ports clk]

# 464MHz (DSPの限界)
# create_clock -period 2.155 -name clk -waveform {0.000 1.0775} [get_ports clk]

# 388MHz (BRAMの限界)
# create_clock -period 2.577 -name clk -waveform {0.000 1.2885} [get_ports clk]

# 333MHz
# create_clock -period 3.000 -name clk -waveform {0.000 1.5000} [get_ports clk]

# 250MHz (PS-PL のAXIの限界)
create_clock -period 4.000 -name clk -waveform {0.000 2.0000} [get_ports clk]
