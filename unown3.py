from lcrng import PokeRNG

characters = [ "A", "B", "C", "D", "E", "F", "G", "H", "I", "J", "K", "L", "M", "N", "O", "P", "Q", "R", "S", "T", "U", "V", "W", "X", "Y", "Z", "!", "?" ]
natures = [ "Hardy", "Lonely", "Brave", "Adamant", "Naughty", "Bold", "Docile", "Relaxed", "Impish", "Lax", "Timid", "Hasty", "Serious", "Jolly", "Naive", "Modest", "Mild", "Quiet", "Bashful", "Rash", "Calm", "Gentle", "Sassy", "Careful", "Quirky" ]
hiddenPowers = [ "Fighting", "Flying", "Poison", "Ground", "Rock", "Bug", "Ghost", "Steel", "Fire", "Water", "Grass", "Electric", "Psychic", "Ice", "Dragon", "Dark" ]

def getLetter(pid: int):
    letter = (((pid & 0x3000000) >> 18) | ((pid & 0x30000) >> 12) | ((pid & 0x300) >> 6) | (pid & 0x3)) % 28
    return characters[letter]

def getTargetLetter(location: int, slot: int):
    if location == 0:
        if slot < 99:
            return "A"
        else:
            return "?"
    elif location == 1:
        if slot < 50:
            return "C"
        elif slot < 80:
            return "D"
        elif slot < 94:
            return "H"
        elif slot < 99:
            return "U"
        else:
            return "O"
    elif location == 2:
        if slot < 60:
            return "N"
        elif slot < 90:
             return "S"
        elif slot < 98:
            return "I"
        else:
            return "E"
    elif location == 3:
        if slot < 40:
            return "P"
        elif slot < 60:
            return "L"
        elif slot < 80:
            return "J"
        elif slot < 94:
            return "R"
        else:
            return "Q"
    elif location == 4:
        if slot < 40:
            return "Y"
        elif slot < 60:
            return "T"
        elif slot < 85:
            return "G"
        elif slot < 98:
            return "F"
        else:
            return "K"
    elif location == 5:
        if slot < 50:
            return "V"
        elif slot < 80:
            return "W"
        elif slot < 90:
            return "X"
        elif slot < 98:
            return "M"
        else:
            return "B"
    elif location == 6:
        if slot < 99:
            return "Z"
        else:
            return "!"

def getIVs(iv1: int, iv2: int):
    hp = iv1 & 0x1f
    atk = (iv1 >> 5) & 0x1f
    defense = (iv1 >> 10) & 0x1f
    spa = (iv2 >> 5) & 0x1f
    spd = (iv2 >> 10) & 0x1f
    spe = iv2 & 0x1f
    return [ hp, atk, defense, spa, spd, spe ]

def getShiny(tsv: int, pid: int):
    return (pid & 0xffff) ^ (pid >> 16) ^ tsv < 8

if __name__ == "__main__":
    print("Monean Chamber  - 0 (Letters: A, ?)")
    print("Liptoo Chamber  - 1 (Letters: C, D, H, U, O)")
    print("Weepth Chamber  - 2 (Letters: N, S, I, E)")
    print("Dilford Chamber - 3 (Letters: P, J, L, R, Q)")
    print("Scufib Chamber  - 4 (Letters: Y, G, T, F, K)")
    print("Rixy Chamber    - 5 (Letters: V, W, X, M, B)")
    print("Viapois Chamber - 6 (Letters: Z, !)")
    print("")

    seed = int(input("Enter initial seed: 0x"), 16)

    location = int(input("Enter location number: "))    
    while location < 0 or location > 6:
        print("Invalid input")
        location = int(input("Enter location number: "))

    startFrame = int(input("Enter starting frame: "))
    maxFrame = int(input("Enter max frame: "))

    tid = int(input("Enter TID: "))
    if tid < 0 or tid > 65535:
        print("Invalid input")
        tid = int(input("Enter TID: "))

    sid = int(input("Enter SID: "))
    if sid < 0 or sid > 65535:
        print("Invalid input")
        sid = int(input("Enter SID: "))

    shiny = int(input("Shiny only(1/0): "))
    if shiny != 0 and shiny != 1:
        print("Invalid input")
        shiny = int(input("Shiny only(1/0): "))

    nature = int(input("Enter nature value as a number(-1 for any): "))
    if nature < -1 or nature > 24:
        print("Invalid input")
        nature = int(input("Enter nature value as a number(-1 for any): "))

    print("")
    print("Enter ivs in the format such as X.X.X.X.X.X where X is the numbers")
    minIVs = [int(val) for val in input("Enter min IVs: ").split(".")]
    maxIVs = [int(val) for val in input("Enter max IVs: ").split(".")]

    print("")
    tsv = tid ^ sid
    rng = PokeRNG(seed)
    rng.advance_frames(startFrame - 1)
        
    for cnt in range(maxFrame):
        flag = True
        go = PokeRNG(rng.next_uint()) # Blank

        slot = go.next_ushort() % 100
        targetLetter = getTargetLetter(location, slot)

        go.next_uint() # Blank

        letter = ""
        pid = 0
        while letter != targetLetter:
            high = go.next_ushort()
            low = go.next_ushort()

            pid = (high << 16) | low
            letter = getLetter(pid)

        iv1 = go.next_ushort()
        iv2 = go.next_ushort()
        ivs = getIVs(iv1, iv2)

        if nature != -1 and nature != pid % 25:
            flag = False

        for i in range(6):
            if ivs[i] < minIVs[i] or ivs[i] > maxIVs[i]:
                flag = False
                break

        if shiny == 1 and not getShiny(tsv, pid):
            flag = False
        
        if flag:
            print("Frame: " + str(cnt + startFrame))
            print("Letter: " + targetLetter)
            print("PID: " + hex(pid) + "\t Nature: " + natures[pid % 25])
            print("IVs: " + str(ivs))
            print("")
        
