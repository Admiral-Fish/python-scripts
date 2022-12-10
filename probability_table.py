from lcrng import BWRNG


def probability_table(rng: BWRNG):
    count = 0

    # Round 1
    count += 1
    rng.advance_frames(1)

    # Round 2
    count += 1
    if rng.next_uint(101) > 50:
        count += 1
        rng.advance_frames(1)

    # Round 3
    count += 1
    if rng.next_uint(101) > 30:
        count += 1
        rng.advance_frames(1)

    # Round 4
    count += 1
    if rng.next_uint(101) > 25:
        count += 1
        if rng.next_uint(101) > 30:
            count += 1
            rng.advance_frames(1)

    # Round 5
    count += 1
    if rng.next_uint(101) > 20:
        count += 1
        if rng.next_uint(101) > 25:
            count += 1
            if rng.next_uint(101) > 33:
                count += 1
                rng.advance_frames(1)

    return count


def pid_advances(seed):
    count = 0

    rng = BWRNG(seed)
    for _ in range(5):
        count += probability_table(rng)

    return count


if __name__ == "__main__":
    pid_advances(0xb082b4a755192171)
