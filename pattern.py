from lcrng import XDRNGR

def get_target(rng: XDRNGR, index: int):    
    '''    
    mask = 1 << (rng.next_ushort() >> 14)
    while (mask & 14) != 14:
        mask |= 1 << (rng.next_ushort() >> 14)

    thresh = [ 0x4000, 0x547a ]
    rng.advance_frames(4)
    flag = false
    for i in range(2):
        rand = rng.next_ushort()
        if rand <= thresh[i]
            flag = true
            break
    rng.advance_frames(flag ? 1 : 2)

    # Proceed to generate jirachi
    '''
    
    if index == 0: # 6 advances total
        rng.advance_frames(1)
        if rng.next_ushort() <= 0x4000:
            rng.advance_frames(4)
            return True
    elif index == 1: # 7 advances total
        rng.advance_frames(1)
        if rng.next_ushort() <= 0x547a:
            if rng.next_ushort() > 0x4000:
                rng.advance_frames(4)
                return True
    elif index == 2: # 8 advances total
        rng.advance_frames(2)
        if rng.next_ushort() > 0x547a:
            if rng.next_ushort() > 0x4000:
                rng.advance_frames(4)
                return True
    
    return False

def check_seed(seed: int):
    # Jirachi floating into the screen has 3 different patterns to follow
    # Check each of them
    for i in range(3):
        rng = XDRNGR(seed)
        if get_target(rng, i):
            # Menu can't end on 0
            target = rng.seed >> 30
            if target != 0:
                # From start, game advances until (prng >> 30) gives a 1, 2, and 3
                # (prng >> 30) giving 0 is just filler
                mask = 1 << target

                # Work backwards to determine if spread is possible
                # If we encounter target again before rolling a 1, 2, and 3 then the seed isn't legal
                while True:
                    rand = rng.next_ushort() >> 14

                    # Seed under current pattern isn't possible
                    # Continue on with other patterns
                    if rand == target:
                        break

                    mask |= 1 << rand

                    # Encountered a 1, 2, and 3
                    # Seed is legal
                    if (mask & 14) == 14:
                        return True

    return False

if __name__ == "__main__":
    seed = int(input("Seed: 0x"), 16)
    flag = check_seed(seed)

    if flag:
        print(f"{hex(seed)} is legal")
    else:
        print(f"{hex(seed)} isn't legal")