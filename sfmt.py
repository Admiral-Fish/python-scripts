def uint(num: int):
    return num & 0xFFFFFFFF


class SFMT:
    def __init__(self, seed: int):
        self.state = [0]*624
        self.index = 624

        # Initialize
        self.state[0] = seed
        for i in range(1, 624):
            y = 0x6C078965 * (self.state[i-1] ^ (self.state[i-1] >> 30)) + i
            self.state[i] = uint(y)

        # Period certification
        inner = 0

        parity = (0x1, 0x0, 0x0, 0x13c9e684)
        for i in range(4):
            inner ^= self.state[i] & parity[i]

        i = 16
        while i > 0:
            inner ^= inner >> i
            i >>= 1

        if (inner & 1) == 1:
            return

        work = 0
        for i in range(4):
            work = 1
            for _ in range(32):
                if ((work & parity[i]) != 0):
                    self.state[i] ^= work
                    return
                work <<= 1

    def shuffle(self):
        a = 0
        b = 488
        c = 616
        d = 620

        while a < 624:
            self.state[a + 3] ^= uint(self.state[a + 3] << 8)
            self.state[a + 3] ^= self.state[c + 3] >> 8
            self.state[a + 3] ^= (self.state[b + 3] >> 11) & 0xbffffff6
            self.state[a + 3] ^= uint(self.state[d + 3] << 18)
            self.state[a + 3] ^= self.state[a + 2] >> 24

            self.state[a + 2] ^= uint(self.state[a + 2] << 8)
            self.state[a + 2] ^= self.state[c + 2] >> 8
            self.state[a + 2] ^= (self.state[b + 2] >> 11) & 0xbffaffff
            self.state[a + 2] ^= uint(self.state[d + 2] << 18)
            self.state[a + 2] ^= self.state[a + 1] >> 24
            self.state[a + 2] ^= uint(self.state[c + 3] << 24)

            self.state[a + 1] ^= uint(self.state[a + 1] << 8)
            self.state[a + 1] ^= self.state[c + 1] >> 8
            self.state[a + 1] ^= (self.state[b + 1] >> 11) & 0xddfecb7f
            self.state[a + 1] ^= uint(self.state[d + 1] << 18)
            self.state[a + 1] ^= self.state[a] >> 24
            self.state[a + 1] ^= uint(self.state[c + 2] << 24)

            self.state[a] ^= uint(self.state[a] << 8)
            self.state[a] ^= self.state[c] >> 8
            self.state[a] ^= (self.state[b] >> 11) & 0xdfffffef
            self.state[a] ^= uint(self.state[d] << 18)
            self.state[a] ^= uint(self.state[c + 1] << 24)

            c = d
            d = a
            a += 4
            b += 4
            if b >= 624:
                b = 0
        self.index -= 624

    def next(self):
        if self.index >= 624:
            self.shuffle()

        result = self.state[self.index]
        self.index += 1

        return result


if __name__ == "__main__":
    rng = SFMT(0)
    for i in range(10):
        print(hex(rng.next()))
