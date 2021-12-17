class MersenneTwister:
    def __init__(self, seed: int):
        self.state = [seed]
        self.index = 624

        for i in range(1, 624):
            y = 0x6C078965 * (self.state[i - 1] ^ (self.state[i - 1] >> 30)) + i
            self.state.append(y & 0xFFFFFFFF)

        print(self.state)

    def next(self):
        if self.index >= 624:
            self.shuffle()

        y = self.state[self.index]
        self.index += 1

        y ^= (y >> 11)
        y ^= ((y << 7) & 0xFFFFFFFF) & 0x9D2C5680
        y ^= ((y << 15) & 0xFFFFFFFF) & 0xEFC60000
        y ^= (y >> 18)

        return y

    def shuffle(self):
        for i in range(624):
            y = (self.state[i] & 0x80000000) | (self.state[(i + 1) % 624] & 0x7FFFFFFF)
            next = y >> 1

            if y & 1 == 1:
                next ^= 0x9908b0df

            self.state[i] = next ^ self.state[(i + 397) % 624]
        self.index -= 624

if __name__ == "__main__":
    rng = MersenneTwister(0)
    for i in range(10):
        rng.next()