import struct


class PK8:
    def __init__(self, data: bytes):
        self.data = data

    def getEC(self) -> int:
        return struct.unpack("<I", self.data[0x0:0x4])[0]

    def getTID(self) -> int:
        return struct.unpack("<H", self.data[0xC:0xE])[0]

    def getSID(self) -> int:
        return struct.unpack("<H", self.data[0xE:0x10])[0]

    def getPID(self) -> int:
        return struct.unpack("<I", self.data[0x1C:0x20])[0]

    def getIV(self) -> int:
        return struct.unpack("<I", self.data[0x8C:0x90])[0]

    def getHP(self) -> int:
        return self.getIV() & 0x1F

    def getAtk(self) -> int:
        return (self.getIV() >> 5) & 0x1F

    def getDef(self) -> int:
        return (self.getIV() >> 10) & 0x1F

    def getSpA(self) -> int:
        return (self.getIV() >> 20) & 0x1F

    def getSpD(self) -> int:
        return (self.getIV() >> 25) & 0x1F

    def getSpe(self) -> int:
        return (self.getIV() >> 15) & 0x1F

    def getNature(self) -> int:
        return self.data[0x20]

    def getAbility(self) -> int:
        return (self.data[0x16] & 7) >> 1
