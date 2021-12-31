def uint(value: int):
    return value & 0xFFFFFFFF

def reverse_xor_left_shift(value: int, shift: int):
    i = 0

    while i * shift < 32:
        partMask = uint(0xFFFFFFFF >> (32 - shift)) << (shift * i)
        part = value & partMask
        value ^= uint(part << shift)
        i += 1

    return value

def reverse_xor_right_shift(value: int, shift: int):
    i = 0
    result = 0

    while i * shift < 32:
        partMask = uint(0xFFFFFFFF << (32 - shift)) >> (shift * i)
        part = value & partMask
        value ^= part >> shift
        result |= part
        i += 1

    return result

def reverse(state):
    t = state[3]
    s = state[2]

    # undo t ^= s ^ (s >> 19)
    t ^= s ^ (s >> 19)

    # undo t ^= t >> 8
    t = reverse_xor_right_shift(t, 8)

    # undo t ^= (t << 11) & 0xffffffff
    t = reverse_xor_left_shift(t, 11)

    state[3] = state[2]
    state[2] = state[1]
    state[1] = state[0]
    state[0] = t

    return state


if __name__ == "__main__":
    states = [0x12345678, 0x12345678, 0x87654321, 0x87654321]

    for i in range(2):
        states = reverse(states)
        print([hex(x) for x in states])
