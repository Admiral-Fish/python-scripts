def uint(num: int):
    return num & 0xFFFFFFFF


def unBitshiftRightXor(value: int, shift: int):
    i = 0
    result = 0

    while i * shift < 32:
        partMask = uint(0xFFFFFFFF << (32 - shift)) >> (shift * i)
        part = value & partMask
        value ^= part >> shift
        result |= part
        i += 1

    return result


def unBitshiftLeftXor(value: int, shift: int):
    i = 0
    result = 0

    while i * shift < 32:
        partMask = uint((0xFFFFFFFF >> (32 - shift)) << (shift * i))
        part = value & partMask
        value ^= ((part << shift) & 0xFFFFFFFF)
        result |= part
        i += 1

    return result


def reverse(s: list[int]):
    y = s[3]
    state1 = s[0]

    if y & 1 == 1:
        s[1] ^= 0x8f7011ee
        s[2] ^= 0xfc78ff1f

    state2 = s[1]

    x = s[2] ^ uint(y << 10)

    state3 = unBitshiftRightXor(y ^ x, 1)
    x = unBitshiftLeftXor(x, 1)

    state0 = x ^ state1 ^ state2

    return [state0, state1, state2, state3]


def advance(s: list[int]):
    y = s[3]
    x = (s[0] & 0x7FFFFFFF) ^ s[1] ^ s[2]
    x ^= uint(x << 1)
    y ^= (y >> 1) ^ x
    s[0] = s[1]
    s[1] = s[2]
    s[2] = x ^ uint(y << 10)
    s[3] = y

    if y & 1 == 1:
        s[1] ^= 0x8f7011ee
        s[2] ^= 0xfc78ff1f

    return s


def reverseInit(s: list[int]):
    for _ in range(8):
        if _ == 7:
            x = 5
        s = reverse(s.copy())

        s1 = reverse(reverse(reverse(s.copy())))
        s1 = advance(advance(advance(s1.copy())))
        if s != s1:
            s[0] ^= 0x80000000

        printState(s)

    # Assume period_certification did nothing

    for i in range(7, 0, -1):
        y = 0x6c078965 * (s[(i - 1) & 3] ^ (s[(i - 1) & 3] >> 30)) + i
        s[i & 3] ^= y & 0xFFFFFFFF

    return s


def reverseTinyMTTIDSID(s: list[int]):
    for _ in range(2):
        s = reverse(s.copy())

        s1 = reverse(reverse(reverse(s.copy())))
        s1 = advance(advance(advance(s1.copy())))
        if s != s1:
            s[0] ^= 0x80000000

        printState(s)

    s = reverseInit(s.copy())
    return s


def printState(s: list[int]):
    print([hex(state) for state in s])


if __name__ == "__main__":
    s = [0xf960f823, 0x134cd665, 0xd81408bb, 0xd04eac92]
    s = reverseTinyMTTIDSID(s.copy())
    #print([hex(state) for state in s])
    # ['0x18a', '0x8f7011ee', '0xfc78ff1f', '0x3793fdff']
