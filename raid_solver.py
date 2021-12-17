import sys
import z3

from pk8 import PK8
from xoroshiro import Xoroshiro

def sym_xoroshiro128plus(start_s0, start_s1):
    result = (start_s0 + start_s1) & 0xFFFFFFFF

    start_s1 ^= start_s0
    start_s0 = z3.RotateLeft(start_s0, 24) ^ start_s1 ^ ((start_s1 << 16) & 0xFFFFFFFFFFFFFFFF)
    start_s1 = z3.RotateLeft(start_s1, 37)

    return start_s0, start_s1, result

def get_models(s: z3.Solver):
    while s.check() == z3.sat:
        m = s.model()
        yield m
        
        # Constraint that makes current answer invalid
        d = m[0]
        c = d()
        s.add(c != m[d])

def find_seeds(ec, pid):
    solver = z3.Solver()

    start_s0 = z3.BitVec('start_s0', 64)
    start_s1 = z3.BitVecVal(0x82A2B175229D6A5B, 64)

    # EC call
    start_s0, start_s1, result_ec = sym_xoroshiro128plus(start_s0, start_s1)

    # TID/SID call
    start_s0, start_s1, _ = sym_xoroshiro128plus(start_s0, start_s1)

    # PID call
    start_s0, start_s1, result_pid = sym_xoroshiro128plus(start_s0, start_s1)

    solver.add(result_ec == ec)
    solver.add(result_pid == pid)
        
    return get_models(solver)

def find_seed(seeds, ivs):
    for seed in seeds:
        for iv_count in range(1, 6):
            rng = Xoroshiro(seed)

            # ec, tid/sid, pid
            for i in range(3):
                rng.nextInt(0xffffffff, 0xffffffff)

            check_ivs = [None]*6
            count = 0
            while count < iv_count:
                stat = rng.nextInt(6, 7)
                if check_ivs[stat] is None:
                    check_ivs[stat] = 31
                    count += 1

            for i in range(6):
                if check_ivs[i] is None:
                    check_ivs[i] = rng.nextInt(32, 31)

            if ivs == check_ivs:
                return seed, iv_count

    return None, None

def search(ec, pid, ivs):
    print("")
    seeds = find_seeds(ec, pid)
    seed, iv_count = find_seed(seeds, ivs)
    if seed != None:
        print(f"Raid seed: {hex(seed)} with IV count of {iv_count}")
        return True

    seedsXor = find_seeds(ec, pid ^ 0x10000000) # Check for shiny lock
    seed, iv_count = find_seed(seedsXor, ivs)
    if seed != None:
        print(f"Raid seed (shiny locked): {hex(seed)} with IV count of {iv_count}")
        return True

    return False

def searchPKM():
    file_name = sys.argv[1]
    with open(file_name, "rb") as f:
        data = f.read()
    pkm = PK8(data)

    ec = pkm.getEC()
    pid = pkm.getPID()
    ivs = [ pkm.getHP(), pkm.getAtk(), pkm.getDef(), pkm.getSpA(), pkm.getSpD(), pkm.getSpe() ]

    return search(ec, pid, ivs)

def searchInput():
    ec = int(input("Enter EC: 0x"), 16)
    pid = int(input("Enter PID: 0x"), 16)
    ivs = [ int(iv) for iv in input("Enter IVs(x.x.x.x.x.x): ").split(".") ]

    return search(ec, pid, ivs)

def main():
    if len(sys.argv) == 1:
        return searchInput()
    else:
        return searchPKM()

if __name__ == "__main__":
    if main() == False:
        print("No raid seed")
        print("This means one of three things")
        print("1. You entered something wrong")
        print("2. This script does not check for forced shiny since that takes a long time to compute. Try again with a non-shiny raid")
        print("3. You encountered an extremely rare edge case (odds are you fall under case 1 though)")
    
    input("Press ENTER to exit")
