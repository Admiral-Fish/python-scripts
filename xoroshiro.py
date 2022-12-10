class Xoroshiro:
    def __init__(self, seed):
        self.seed = [seed, 0x82A2B175229D6A5B]

    @staticmethod
    def rotl(x, k):
        return ((x << k) | (x >> (64 - k))) & 0xFFFFFFFFFFFFFFFF

    def _next(self):
        s0, s1 = self.seed
        result = (s0 + s1) & 0xFFFFFFFFFFFFFFFF

        s1 ^= s0
        self.seed[0] = self.rotl(s0, 24) ^ s1 ^ ((s1 << 16) & 0xFFFFFFFFFFFFFFFF)
        self.seed[1] = self.rotl(s1, 37)

        return result

    def next_int(self, thresh, mask=None):
        if mask is None:
            return self.next() & thresh

        result = self._next() & mask
        while result >= thresh:
            result = self._next() & mask
        return result


class XoroshiroBDSP:
    def __init__(self, seed: int):
        self.seed = [self._splitmix(seed, 0x9E3779B97F4A7C15), self._splitmix(seed, 0x3C6EF372FE94F82A)]

    @staticmethod
    def _splitmix(seed: int, state: int):
        seed += state
        seed = (0xBF58476D1CE4E5B9 * (seed ^ (seed >> 30))) & 0xFFFFFFFFFFFFFFFF
        seed = (0x94D049BB133111EB * (seed ^ (seed >> 27))) & 0xFFFFFFFFFFFFFFFF
        return seed ^ (seed >> 31)

    @staticmethod
    def _rotl(x: int, k: int):
        return ((x << k) | (x >> (64 - k))) & 0xFFFFFFFFFFFFFFFF

    def next(self, max: int = None):
        s0, s1 = self.seed
        result = (s0 + s1) & 0xFFFFFFFFFFFFFFFF

        s1 ^= s0
        self.seed[0] = self._rotl(s0, 24) ^ s1 ^ ((s1 << 16) & 0xFFFFFFFFFFFFFFFF)
        self.seed[1] = self._rotl(s1, 37)

        if max:
            return (result >> 32) % max
        else:
            return (result >> 32)


if __name__ == "__main__":
    rng = Xoroshiro(0)

    for _ in range(100):
        print(hex(rng.nextInt(0xffffffff)))

    rng = XoroshiroBDSP(0)

    for _ in range(100):
        print(hex(rng.nextInt(0xffffffff)))
