from io import BufferedReader
import struct


class Narc:
    def __init__(self, path: str):
        file = open(path, "rb")
        self.read_offsets(file)
        self.read_elements(file)
        file.close()

    def read_offsets(self, file: BufferedReader):
        self.fat_b_offset = 0x10

        file.seek(0x18)
        self.fnt_b_offset = struct.unpack("<I", file.read(4))[0] * 8 + self.fat_b_offset + 12

        file.seek(self.fnt_b_offset + 4)
        self.fimg_offset = struct.unpack("<I", file.read(4))[0] + self.fnt_b_offset

    def read_elements(self, file: BufferedReader):
        file.seek(0x18)
        number_of_elements, = struct.unpack("<I", file.read(4))

        self.elements = []
        start_offsets = []
        end_offsets = []

        file.seek(self.fat_b_offset + 0xc)
        for _ in range(number_of_elements):
            start_offsets.append(struct.unpack("<I", file.read(4))[0])
            end_offsets.append(struct.unpack("<I", file.read(4))[0])

        for i in range(number_of_elements):
            file.seek(self.fimg_offset + start_offsets[i] + 8)
            self.elements.append(file.read(end_offsets[i] - start_offsets[i]))

    def get_elements(self) -> list:
        return self.elements
