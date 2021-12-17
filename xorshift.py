class Xorshift:
    def __init__(self, seed0: int, seed1: int):
        self.seed = [seed0 >> 32, seed0 & 0xffffffff, seed1 >> 32, seed1 & 0xffffffff]

    def next(self):
        t = self.seed[0]
        s = self.seed[3]

        t ^= (t << 11) & 0xffffffff
        t ^= t >> 8
        t ^= s ^ (s >> 19)

        self.seed[0] = self.seed[1]
        self.seed[1] = self.seed[2]
        self.seed[2] = self.seed[3]
        self.seed[3] = t

        return ((t % 0xffffffff) + 0x80000000) & 0xffffffff

if __name__ == "__main__":
    rng = Xorshift(0x52e76d830ba18b83, 0xa587b502ad523f9d)

    for _ in range(5):
        rng.next()
