from typing import Union

def uint(num: int):
    return num & 0xffffffff

class TinyMT:
    def __init__(self, seed: Union[int, list[int]]):
        if type(seed) is int:
            self.state = [seed, 0x8f7011ee, 0xfc78ff1f, 0x3793fdff]
            self.init()
        elif type(seed) is list:
            self.state = seed
        else:
            raise ValueError("Argument must be a 32bit number or a list with 4 32bit numbers")
    
    def init(self):
        for i in range(1, 8):
            y = 0x6c078965 * (self.state[(i-1) & 3] ^ (self.state[(i-1) & 3]) >> 30) + i
            self.state[i & 3] ^= uint(y)

        # Period certification
        if (self.state[0] & 0x7FFFFFFF) == 0 and self.state[1] == 0 and self.state[2] == 0 and self.state[3] == 0:
            self.state[0] = 84
            self.state[1] = 73
            self.state[2] = 78
            self.state[3] = 89

        for i in range(8):
            self._next_state()

    def next_uint(self):
        self._next_state()
        return self._temper()

    def _next_state(self):
        y = self.state[3]
        x = (self.state[0] & 0x7FFFFFFF) ^ self.state[1] ^ self.state[2]
        x ^= uint(x << 1)
        y ^= (y >> 1) ^ x
        self.state[0] = self.state[1]
        self.state[1] = self.state[2]
        self.state[2] = x ^ uint(y << 10)
        self.state[3] = y

        if y & 1 == 1:
            self.state[1] ^= 0x8f7011ee
            self.state[2] ^= 0xfc78ff1f

    def _temper(self):
        t0 = self.state[3]
        t1 = uint(self.state[0] + (self.state[2] >> 8))

        t0 ^= t1
        if t1 & 1 == 1:
            t0 ^= 0x3793fdff

        return t0

if __name__ == "__main__":
    rng = TinyMT(0x0)
    #rng = TinyMT([0x8c52a334, 0x4bb1ee2f, 0x7610e9cd, 0xa192c672])
    for i in range(10):
        print(hex(rng.next_uint()))
