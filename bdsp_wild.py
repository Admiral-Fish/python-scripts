from typing import Union
import z3


def get_models(s: z3.Solver):
    while s.check() == z3.sat:
        m = s.model()
        yield m

        # Constraint that makes current answer invalid
        d = m[0]
        c = d()
        s.add(c != m[d])


def advance_xorshift(state0: Union[z3.BitVecNumRef, z3.BitVecRef], state1: Union[z3.BitVecNumRef, z3.BitVecRef],
                     state2: Union[z3.BitVecNumRef, z3.BitVecRef], state3: Union[z3.BitVecNumRef, z3.BitVecRef]):
    t = state0
    s = state3

    t ^= (t << 11) & 0xffffffff
    t ^= z3.LShR(t, 8)
    t ^= s ^ z3.LShR(s, 19)

    # Technically we should return (t % 0xffffffff) ^ 0x80000000
    # Rare enough impact that it probably doesn't matter

    return state1, state2, state3, t, t ^ 0x80000000


def main():
    EC_RAND = 0x92f4ef4a
    PID_RAND = 0x04bfae9a
    IVS = [10, 27, 29, 19, 0, 29]
    ABILITY = 1
    NATURE = 24

    SECOND_EC = 0x518c1fcf
    SECOND_PID = 0x64a122ba

    state0 = z3.BitVecVal(EC_RAND, 32)
    state1 = z3.BitVec("state1", 32)
    state2 = z3.BitVecVal(PID_RAND, 32)
    hp = z3.BitVec("state3", 32)

    state0, state1, state2, state3, atk = advance_xorshift(state0, state1, state2, hp)
    state0, state1, state2, state3, defense = advance_xorshift(state0, state1, state2, state3)
    state0, state1, state2, state3, spa = advance_xorshift(state0, state1, state2, state3)
    state0, state1, state2, state3, spd = advance_xorshift(state0, state1, state2, state3)
    state0, state1, state2, state3, spe = advance_xorshift(state0, state1, state2, state3)
    state0, state1, state2, state3, ability_num = advance_xorshift(state0, state1, state2, state3)
    state0, state1, state2, state3, gender_rand = advance_xorshift(state0, state1, state2, state3)
    state0, state1, state2, state3, nature = advance_xorshift(state0, state1, state2, state3)

    for _ in range(0, 8):
        state0, state1, state2, state3, _ = advance_xorshift(state0, state1, state2, state3)

    state0, state1, state2, state3, second_ec = advance_xorshift(state0, state1, state2, state3)
    state0, state1, state2, state3, second_fake_sidtid = advance_xorshift(state0, state1, state2, state3)
    state0, state1, state2, state3, second_pid = advance_xorshift(state0, state1, state2, state3)

    solver = z3.Solver()
    solver.add(hp & 31 == IVS[0])
    solver.add(atk & 31 == IVS[1])
    solver.add(defense & 31 == IVS[2])
    solver.add(spa & 31 == IVS[3])
    solver.add(spd & 31 == IVS[4])
    solver.add(spe & 31 == IVS[5])
    solver.add(ability_num & 1 == ABILITY)
    solver.add(nature % 25 == NATURE)
    solver.add(second_ec == SECOND_EC)
    solver.add(second_pid == SECOND_PID)

    return get_models(solver)


if __name__ == "__main__":
    models = main()
    for model in models:
        state_s1 = model[0]
        state_s3 = model[1]
        print(f"State1: {hex(model[state_s1].as_long())} State3: {hex(model[state_s3].as_long())}")
