from lcrng import RanchRNG

# 0: Zoom in
# 1: Upper right to lower left
# 2: Start high, up to bottom
# 3: Left to right
# 4: Start high, zoom in
# 5: Zoom out
# 6: Up to bottom
cameras = [0, 0, 1, 0, 2, 3, 4, 5, 5, 6]

# Input at least 13 camera entries
# Focus lock is a must
inputs = [0, 0, 5, 4, 2, 1, 5, 4, 1, 0, 4, 1, 6]

for seed in range(0x80000000):
    rng = RanchRNG(seed)

    flag = True

    for entry in inputs:
        rand = rng.next_ushort() % 10
        camera = cameras[rand]

        if camera != entry:
            flag = False
            break

        rng.advance_frames(2)

    if flag:
        print(hex(rng.seed))
