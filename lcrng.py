class LCRNG:
    def __init__(self, seed: int, mult: int, add: int):
        self.seed = seed
        self.mult = mult
        self.add = add

    def advance_frames(self, frames: int):
        for _ in range(frames):
            self.next_uint()

    def next_uint(self):
        self.seed = (self.seed * self.mult + self.add) & 0xffffffff
        return self.seed

    def next_ushort(self):
        return self.next_uint() >> 16


class LCRNG64:
    def __init__(self, seed: int, mult: int, add: int):
        self.seed = seed
        self.mult = mult
        self.add = add

    def advance_frames(self, frames: int):
        for _ in range(frames):
            self.next_uint()

    def next_ulong(self):
        self.seed = (self.seed * self.mult + self.add) & 0xffffffffffffffff
        return self.seed

    def next_uint(self, max: int = None):
        rand = self.next_ulong() >> 32
        if max is not None:
            rand = (rand * max) >> 32
        return rand


class XDRNG(LCRNG):
    def __init__(self, seed: int):
        LCRNG.__init__(seed, 0x343FD, 0x269EC3)


class XDRNGR(LCRNG):
    def __init__(self, seed: int):
        LCRNG.__init__(seed, 0xB9B33155, 0xA170F641)


class PokeRNG(LCRNG):
    def __init__(self, seed: int):
        LCRNG.__init__(seed, 0x41C64E6D, 0x6073)


class PokeRNGR(LCRNG):
    def __init__(self, seed: int):
        LCRNG.__init__(seed, 0xEEB9EB65, 0xA3561A1)

class RanchRNG(LCRNG):
    def __init__(self, seed: int):
        LCRNG.__init__(seed, 0x41C64E6D, 0x3039)

    def next_ushort(self):
        return (self.next_uint() >> 16) & 0x7fff

class RanchRNGR(LCRNG):
    def __init__(self, seed: int):
        LCRNG.__init__(seed, 0xEEB9EB65, 0xFC77A683)

    def next_ushort(self):
        return (self.next_uint() >> 16) & 0x7fff


class ARNG(LCRNG):
    def __init__(self, seed: int):
        LCRNG.__init__(seed, 0x6C078965, 0x01)


class ARNGR(LCRNG):
    def __init__(self, seed: int):
        LCRNG.__init__(seed, 0x9638806D, 0x69C77F93)


class BWRNG(LCRNG64):
    def __init__(self, seed: int):
        LCRNG64.__init__(seed, 0x5d588b656c078965, 0x269ec3)


class BWRNGR(LCRNG64):
    def __init__(self, seed: int):
        LCRNG64.__init__(seed, 0xdedcedae9638806d, 0x9b1ae6e9a384e6f9)
