import serial
import struct

def float_to_q16_16(x): return int(x * (1 << 16))
def q16_16_to_float(x): return x / (1 << 16)

ser = serial.Serial("COM4", 115200)  # change COM port

# Prepare test batch
batch = [
    10000,   # N
    50,      # M
    float_to_q16_16(100.0),  # S0
    float_to_q16_16(100.0),  # K
    float_to_q16_16(0.05),   # r
    float_to_q16_16(0.2),    # sigma
    float_to_q16_16(1.0)     # T
]

# Send 7 words
for word in batch:
    ser.write(struct.pack("<I" if word >= 0 else "<i", word))

# Read back 7 words
for i in range(7):
    data = ser.read(4)
    val = struct.unpack("<i", data)[0]
    print(f"Echo {i}: 0x{val:08X} → {q16_16_to_float(val) if i >= 2 else val}")
