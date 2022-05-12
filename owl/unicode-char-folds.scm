(define char-folds '(
(#x0041 #x0061)
(#x0042 #x0062)
(#x0043 #x0063)
(#x0044 #x0064)
(#x0045 #x0065)
(#x0046 #x0066)
(#x0047 #x0067)
(#x0048 #x0068)
(#x0049 #x0069)
(#x004a #x006a)
(#x004b #x006b)
(#x004c #x006c)
(#x004d #x006d)
(#x004e #x006e)
(#x004f #x006f)
(#x0050 #x0070)
(#x0051 #x0071)
(#x0052 #x0072)
(#x0053 #x0073)
(#x0054 #x0074)
(#x0055 #x0075)
(#x0056 #x0076)
(#x0057 #x0077)
(#x0058 #x0078)
(#x0059 #x0079)
(#x005a #x007a)
(#x00b5 #x03bc)
(#x00c0 #x00e0)
(#x00c1 #x00e1)
(#x00c2 #x00e2)
(#x00c3 #x00e3)
(#x00c4 #x00e4)
(#x00c5 #x00e5)
(#x00c6 #x00e6)
(#x00c7 #x00e7)
(#x00c8 #x00e8)
(#x00c9 #x00e9)
(#x00ca #x00ea)
(#x00cb #x00eb)
(#x00cc #x00ec)
(#x00cd #x00ed)
(#x00ce #x00ee)
(#x00cf #x00ef)
(#x00d0 #x00f0)
(#x00d1 #x00f1)
(#x00d2 #x00f2)
(#x00d3 #x00f3)
(#x00d4 #x00f4)
(#x00d5 #x00f5)
(#x00d6 #x00f6)
(#x00d8 #x00f8)
(#x00d9 #x00f9)
(#x00da #x00fa)
(#x00db #x00fb)
(#x00dc #x00fc)
(#x00dd #x00fd)
(#x00de #x00fe)
(#x00df #x0073 #x0073)
(#x0100 #x0101)
(#x0102 #x0103)
(#x0104 #x0105)
(#x0106 #x0107)
(#x0108 #x0109)
(#x010a #x010b)
(#x010c #x010d)
(#x010e #x010f)
(#x0110 #x0111)
(#x0112 #x0113)
(#x0114 #x0115)
(#x0116 #x0117)
(#x0118 #x0119)
(#x011a #x011b)
(#x011c #x011d)
(#x011e #x011f)
(#x0120 #x0121)
(#x0122 #x0123)
(#x0124 #x0125)
(#x0126 #x0127)
(#x0128 #x0129)
(#x012a #x012b)
(#x012c #x012d)
(#x012e #x012f)
(#x0130 #x0069 #x0307)
(#x0132 #x0133)
(#x0134 #x0135)
(#x0136 #x0137)
(#x0139 #x013a)
(#x013b #x013c)
(#x013d #x013e)
(#x013f #x0140)
(#x0141 #x0142)
(#x0143 #x0144)
(#x0145 #x0146)
(#x0147 #x0148)
(#x0149 #x02bc #x006e)
(#x014a #x014b)
(#x014c #x014d)
(#x014e #x014f)
(#x0150 #x0151)
(#x0152 #x0153)
(#x0154 #x0155)
(#x0156 #x0157)
(#x0158 #x0159)
(#x015a #x015b)
(#x015c #x015d)
(#x015e #x015f)
(#x0160 #x0161)
(#x0162 #x0163)
(#x0164 #x0165)
(#x0166 #x0167)
(#x0168 #x0169)
(#x016a #x016b)
(#x016c #x016d)
(#x016e #x016f)
(#x0170 #x0171)
(#x0172 #x0173)
(#x0174 #x0175)
(#x0176 #x0177)
(#x0178 #x00ff)
(#x0179 #x017a)
(#x017b #x017c)
(#x017d #x017e)
(#x017f #x0073)
(#x0181 #x0253)
(#x0182 #x0183)
(#x0184 #x0185)
(#x0186 #x0254)
(#x0187 #x0188)
(#x0189 #x0256)
(#x018a #x0257)
(#x018b #x018c)
(#x018e #x01dd)
(#x018f #x0259)
(#x0190 #x025b)
(#x0191 #x0192)
(#x0193 #x0260)
(#x0194 #x0263)
(#x0196 #x0269)
(#x0197 #x0268)
(#x0198 #x0199)
(#x019c #x026f)
(#x019d #x0272)
(#x019f #x0275)
(#x01a0 #x01a1)
(#x01a2 #x01a3)
(#x01a4 #x01a5)
(#x01a6 #x0280)
(#x01a7 #x01a8)
(#x01a9 #x0283)
(#x01ac #x01ad)
(#x01ae #x0288)
(#x01af #x01b0)
(#x01b1 #x028a)
(#x01b2 #x028b)
(#x01b3 #x01b4)
(#x01b5 #x01b6)
(#x01b7 #x0292)
(#x01b8 #x01b9)
(#x01bc #x01bd)
(#x01c4 #x01c6)
(#x01c5 #x01c6)
(#x01c7 #x01c9)
(#x01c8 #x01c9)
(#x01ca #x01cc)
(#x01cb #x01cc)
(#x01cd #x01ce)
(#x01cf #x01d0)
(#x01d1 #x01d2)
(#x01d3 #x01d4)
(#x01d5 #x01d6)
(#x01d7 #x01d8)
(#x01d9 #x01da)
(#x01db #x01dc)
(#x01de #x01df)
(#x01e0 #x01e1)
(#x01e2 #x01e3)
(#x01e4 #x01e5)
(#x01e6 #x01e7)
(#x01e8 #x01e9)
(#x01ea #x01eb)
(#x01ec #x01ed)
(#x01ee #x01ef)
(#x01f0 #x006a #x030c)
(#x01f1 #x01f3)
(#x01f2 #x01f3)
(#x01f4 #x01f5)
(#x01f6 #x0195)
(#x01f7 #x01bf)
(#x01f8 #x01f9)
(#x01fa #x01fb)
(#x01fc #x01fd)
(#x01fe #x01ff)
(#x0200 #x0201)
(#x0202 #x0203)
(#x0204 #x0205)
(#x0206 #x0207)
(#x0208 #x0209)
(#x020a #x020b)
(#x020c #x020d)
(#x020e #x020f)
(#x0210 #x0211)
(#x0212 #x0213)
(#x0214 #x0215)
(#x0216 #x0217)
(#x0218 #x0219)
(#x021a #x021b)
(#x021c #x021d)
(#x021e #x021f)
(#x0220 #x019e)
(#x0222 #x0223)
(#x0224 #x0225)
(#x0226 #x0227)
(#x0228 #x0229)
(#x022a #x022b)
(#x022c #x022d)
(#x022e #x022f)
(#x0230 #x0231)
(#x0232 #x0233)
(#x023a #x2c65)
(#x023b #x023c)
(#x023d #x019a)
(#x023e #x2c66)
(#x0241 #x0242)
(#x0243 #x0180)
(#x0244 #x0289)
(#x0245 #x028c)
(#x0246 #x0247)
(#x0248 #x0249)
(#x024a #x024b)
(#x024c #x024d)
(#x024e #x024f)
(#x0345 #x03b9)
(#x0370 #x0371)
(#x0372 #x0373)
(#x0376 #x0377)
(#x0386 #x03ac)
(#x0388 #x03ad)
(#x0389 #x03ae)
(#x038a #x03af)
(#x038c #x03cc)
(#x038e #x03cd)
(#x038f #x03ce)
(#x0390 #x03b9 #x0308 #x0301)
(#x0391 #x03b1)
(#x0392 #x03b2)
(#x0393 #x03b3)
(#x0394 #x03b4)
(#x0395 #x03b5)
(#x0396 #x03b6)
(#x0397 #x03b7)
(#x0398 #x03b8)
(#x0399 #x03b9)
(#x039a #x03ba)
(#x039b #x03bb)
(#x039c #x03bc)
(#x039d #x03bd)
(#x039e #x03be)
(#x039f #x03bf)
(#x03a0 #x03c0)
(#x03a1 #x03c1)
(#x03a3 #x03c3)
(#x03a4 #x03c4)
(#x03a5 #x03c5)
(#x03a6 #x03c6)
(#x03a7 #x03c7)
(#x03a8 #x03c8)
(#x03a9 #x03c9)
(#x03aa #x03ca)
(#x03ab #x03cb)
(#x03b0 #x03c5 #x0308 #x0301)
(#x03c2 #x03c3)
(#x03cf #x03d7)
(#x03d0 #x03b2)
(#x03d1 #x03b8)
(#x03d5 #x03c6)
(#x03d6 #x03c0)
(#x03d8 #x03d9)
(#x03da #x03db)
(#x03dc #x03dd)
(#x03de #x03df)
(#x03e0 #x03e1)
(#x03e2 #x03e3)
(#x03e4 #x03e5)
(#x03e6 #x03e7)
(#x03e8 #x03e9)
(#x03ea #x03eb)
(#x03ec #x03ed)
(#x03ee #x03ef)
(#x03f0 #x03ba)
(#x03f1 #x03c1)
(#x03f4 #x03b8)
(#x03f5 #x03b5)
(#x03f7 #x03f8)
(#x03f9 #x03f2)
(#x03fa #x03fb)
(#x03fd #x037b)
(#x03fe #x037c)
(#x03ff #x037d)
(#x0400 #x0450)
(#x0401 #x0451)
(#x0402 #x0452)
(#x0403 #x0453)
(#x0404 #x0454)
(#x0405 #x0455)
(#x0406 #x0456)
(#x0407 #x0457)
(#x0408 #x0458)
(#x0409 #x0459)
(#x040a #x045a)
(#x040b #x045b)
(#x040c #x045c)
(#x040d #x045d)
(#x040e #x045e)
(#x040f #x045f)
(#x0410 #x0430)
(#x0411 #x0431)
(#x0412 #x0432)
(#x0413 #x0433)
(#x0414 #x0434)
(#x0415 #x0435)
(#x0416 #x0436)
(#x0417 #x0437)
(#x0418 #x0438)
(#x0419 #x0439)
(#x041a #x043a)
(#x041b #x043b)
(#x041c #x043c)
(#x041d #x043d)
(#x041e #x043e)
(#x041f #x043f)
(#x0420 #x0440)
(#x0421 #x0441)
(#x0422 #x0442)
(#x0423 #x0443)
(#x0424 #x0444)
(#x0425 #x0445)
(#x0426 #x0446)
(#x0427 #x0447)
(#x0428 #x0448)
(#x0429 #x0449)
(#x042a #x044a)
(#x042b #x044b)
(#x042c #x044c)
(#x042d #x044d)
(#x042e #x044e)
(#x042f #x044f)
(#x0460 #x0461)
(#x0462 #x0463)
(#x0464 #x0465)
(#x0466 #x0467)
(#x0468 #x0469)
(#x046a #x046b)
(#x046c #x046d)
(#x046e #x046f)
(#x0470 #x0471)
(#x0472 #x0473)
(#x0474 #x0475)
(#x0476 #x0477)
(#x0478 #x0479)
(#x047a #x047b)
(#x047c #x047d)
(#x047e #x047f)
(#x0480 #x0481)
(#x048a #x048b)
(#x048c #x048d)
(#x048e #x048f)
(#x0490 #x0491)
(#x0492 #x0493)
(#x0494 #x0495)
(#x0496 #x0497)
(#x0498 #x0499)
(#x049a #x049b)
(#x049c #x049d)
(#x049e #x049f)
(#x04a0 #x04a1)
(#x04a2 #x04a3)
(#x04a4 #x04a5)
(#x04a6 #x04a7)
(#x04a8 #x04a9)
(#x04aa #x04ab)
(#x04ac #x04ad)
(#x04ae #x04af)
(#x04b0 #x04b1)
(#x04b2 #x04b3)
(#x04b4 #x04b5)
(#x04b6 #x04b7)
(#x04b8 #x04b9)
(#x04ba #x04bb)
(#x04bc #x04bd)
(#x04be #x04bf)
(#x04c0 #x04cf)
(#x04c1 #x04c2)
(#x04c3 #x04c4)
(#x04c5 #x04c6)
(#x04c7 #x04c8)
(#x04c9 #x04ca)
(#x04cb #x04cc)
(#x04cd #x04ce)
(#x04d0 #x04d1)
(#x04d2 #x04d3)
(#x04d4 #x04d5)
(#x04d6 #x04d7)
(#x04d8 #x04d9)
(#x04da #x04db)
(#x04dc #x04dd)
(#x04de #x04df)
(#x04e0 #x04e1)
(#x04e2 #x04e3)
(#x04e4 #x04e5)
(#x04e6 #x04e7)
(#x04e8 #x04e9)
(#x04ea #x04eb)
(#x04ec #x04ed)
(#x04ee #x04ef)
(#x04f0 #x04f1)
(#x04f2 #x04f3)
(#x04f4 #x04f5)
(#x04f6 #x04f7)
(#x04f8 #x04f9)
(#x04fa #x04fb)
(#x04fc #x04fd)
(#x04fe #x04ff)
(#x0500 #x0501)
(#x0502 #x0503)
(#x0504 #x0505)
(#x0506 #x0507)
(#x0508 #x0509)
(#x050a #x050b)
(#x050c #x050d)
(#x050e #x050f)
(#x0510 #x0511)
(#x0512 #x0513)
(#x0514 #x0515)
(#x0516 #x0517)
(#x0518 #x0519)
(#x051a #x051b)
(#x051c #x051d)
(#x051e #x051f)
(#x0520 #x0521)
(#x0522 #x0523)
(#x0524 #x0525)
(#x0526 #x0527)
(#x0531 #x0561)
(#x0532 #x0562)
(#x0533 #x0563)
(#x0534 #x0564)
(#x0535 #x0565)
(#x0536 #x0566)
(#x0537 #x0567)
(#x0538 #x0568)
(#x0539 #x0569)
(#x053a #x056a)
(#x053b #x056b)
(#x053c #x056c)
(#x053d #x056d)
(#x053e #x056e)
(#x053f #x056f)
(#x0540 #x0570)
(#x0541 #x0571)
(#x0542 #x0572)
(#x0543 #x0573)
(#x0544 #x0574)
(#x0545 #x0575)
(#x0546 #x0576)
(#x0547 #x0577)
(#x0548 #x0578)
(#x0549 #x0579)
(#x054a #x057a)
(#x054b #x057b)
(#x054c #x057c)
(#x054d #x057d)
(#x054e #x057e)
(#x054f #x057f)
(#x0550 #x0580)
(#x0551 #x0581)
(#x0552 #x0582)
(#x0553 #x0583)
(#x0554 #x0584)
(#x0555 #x0585)
(#x0556 #x0586)
(#x0587 #x0565 #x0582)
(#x10a0 #x2d00)
(#x10a1 #x2d01)
(#x10a2 #x2d02)
(#x10a3 #x2d03)
(#x10a4 #x2d04)
(#x10a5 #x2d05)
(#x10a6 #x2d06)
(#x10a7 #x2d07)
(#x10a8 #x2d08)
(#x10a9 #x2d09)
(#x10aa #x2d0a)
(#x10ab #x2d0b)
(#x10ac #x2d0c)
(#x10ad #x2d0d)
(#x10ae #x2d0e)
(#x10af #x2d0f)
(#x10b0 #x2d10)
(#x10b1 #x2d11)
(#x10b2 #x2d12)
(#x10b3 #x2d13)
(#x10b4 #x2d14)
(#x10b5 #x2d15)
(#x10b6 #x2d16)
(#x10b7 #x2d17)
(#x10b8 #x2d18)
(#x10b9 #x2d19)
(#x10ba #x2d1a)
(#x10bb #x2d1b)
(#x10bc #x2d1c)
(#x10bd #x2d1d)
(#x10be #x2d1e)
(#x10bf #x2d1f)
(#x10c0 #x2d20)
(#x10c1 #x2d21)
(#x10c2 #x2d22)
(#x10c3 #x2d23)
(#x10c4 #x2d24)
(#x10c5 #x2d25)
(#x1e00 #x1e01)
(#x1e02 #x1e03)
(#x1e04 #x1e05)
(#x1e06 #x1e07)
(#x1e08 #x1e09)
(#x1e0a #x1e0b)
(#x1e0c #x1e0d)
(#x1e0e #x1e0f)
(#x1e10 #x1e11)
(#x1e12 #x1e13)
(#x1e14 #x1e15)
(#x1e16 #x1e17)
(#x1e18 #x1e19)
(#x1e1a #x1e1b)
(#x1e1c #x1e1d)
(#x1e1e #x1e1f)
(#x1e20 #x1e21)
(#x1e22 #x1e23)
(#x1e24 #x1e25)
(#x1e26 #x1e27)
(#x1e28 #x1e29)
(#x1e2a #x1e2b)
(#x1e2c #x1e2d)
(#x1e2e #x1e2f)
(#x1e30 #x1e31)
(#x1e32 #x1e33)
(#x1e34 #x1e35)
(#x1e36 #x1e37)
(#x1e38 #x1e39)
(#x1e3a #x1e3b)
(#x1e3c #x1e3d)
(#x1e3e #x1e3f)
(#x1e40 #x1e41)
(#x1e42 #x1e43)
(#x1e44 #x1e45)
(#x1e46 #x1e47)
(#x1e48 #x1e49)
(#x1e4a #x1e4b)
(#x1e4c #x1e4d)
(#x1e4e #x1e4f)
(#x1e50 #x1e51)
(#x1e52 #x1e53)
(#x1e54 #x1e55)
(#x1e56 #x1e57)
(#x1e58 #x1e59)
(#x1e5a #x1e5b)
(#x1e5c #x1e5d)
(#x1e5e #x1e5f)
(#x1e60 #x1e61)
(#x1e62 #x1e63)
(#x1e64 #x1e65)
(#x1e66 #x1e67)
(#x1e68 #x1e69)
(#x1e6a #x1e6b)
(#x1e6c #x1e6d)
(#x1e6e #x1e6f)
(#x1e70 #x1e71)
(#x1e72 #x1e73)
(#x1e74 #x1e75)
(#x1e76 #x1e77)
(#x1e78 #x1e79)
(#x1e7a #x1e7b)
(#x1e7c #x1e7d)
(#x1e7e #x1e7f)
(#x1e80 #x1e81)
(#x1e82 #x1e83)
(#x1e84 #x1e85)
(#x1e86 #x1e87)
(#x1e88 #x1e89)
(#x1e8a #x1e8b)
(#x1e8c #x1e8d)
(#x1e8e #x1e8f)
(#x1e90 #x1e91)
(#x1e92 #x1e93)
(#x1e94 #x1e95)
(#x1e96 #x0068 #x0331)
(#x1e97 #x0074 #x0308)
(#x1e98 #x0077 #x030a)
(#x1e99 #x0079 #x030a)
(#x1e9a #x0061 #x02be)
(#x1e9b #x1e61)
(#x1e9e #x0073 #x0073)
(#x1e9e #x00df)
(#x1ea0 #x1ea1)
(#x1ea2 #x1ea3)
(#x1ea4 #x1ea5)
(#x1ea6 #x1ea7)
(#x1ea8 #x1ea9)
(#x1eaa #x1eab)
(#x1eac #x1ead)
(#x1eae #x1eaf)
(#x1eb0 #x1eb1)
(#x1eb2 #x1eb3)
(#x1eb4 #x1eb5)
(#x1eb6 #x1eb7)
(#x1eb8 #x1eb9)
(#x1eba #x1ebb)
(#x1ebc #x1ebd)
(#x1ebe #x1ebf)
(#x1ec0 #x1ec1)
(#x1ec2 #x1ec3)
(#x1ec4 #x1ec5)
(#x1ec6 #x1ec7)
(#x1ec8 #x1ec9)
(#x1eca #x1ecb)
(#x1ecc #x1ecd)
(#x1ece #x1ecf)
(#x1ed0 #x1ed1)
(#x1ed2 #x1ed3)
(#x1ed4 #x1ed5)
(#x1ed6 #x1ed7)
(#x1ed8 #x1ed9)
(#x1eda #x1edb)
(#x1edc #x1edd)
(#x1ede #x1edf)
(#x1ee0 #x1ee1)
(#x1ee2 #x1ee3)
(#x1ee4 #x1ee5)
(#x1ee6 #x1ee7)
(#x1ee8 #x1ee9)
(#x1eea #x1eeb)
(#x1eec #x1eed)
(#x1eee #x1eef)
(#x1ef0 #x1ef1)
(#x1ef2 #x1ef3)
(#x1ef4 #x1ef5)
(#x1ef6 #x1ef7)
(#x1ef8 #x1ef9)
(#x1efa #x1efb)
(#x1efc #x1efd)
(#x1efe #x1eff)
(#x1f08 #x1f00)
(#x1f09 #x1f01)
(#x1f0a #x1f02)
(#x1f0b #x1f03)
(#x1f0c #x1f04)
(#x1f0d #x1f05)
(#x1f0e #x1f06)
(#x1f0f #x1f07)
(#x1f18 #x1f10)
(#x1f19 #x1f11)
(#x1f1a #x1f12)
(#x1f1b #x1f13)
(#x1f1c #x1f14)
(#x1f1d #x1f15)
(#x1f28 #x1f20)
(#x1f29 #x1f21)
(#x1f2a #x1f22)
(#x1f2b #x1f23)
(#x1f2c #x1f24)
(#x1f2d #x1f25)
(#x1f2e #x1f26)
(#x1f2f #x1f27)
(#x1f38 #x1f30)
(#x1f39 #x1f31)
(#x1f3a #x1f32)
(#x1f3b #x1f33)
(#x1f3c #x1f34)
(#x1f3d #x1f35)
(#x1f3e #x1f36)
(#x1f3f #x1f37)
(#x1f48 #x1f40)
(#x1f49 #x1f41)
(#x1f4a #x1f42)
(#x1f4b #x1f43)
(#x1f4c #x1f44)
(#x1f4d #x1f45)
(#x1f50 #x03c5 #x0313)
(#x1f52 #x03c5 #x0313 #x0300)
(#x1f54 #x03c5 #x0313 #x0301)
(#x1f56 #x03c5 #x0313 #x0342)
(#x1f59 #x1f51)
(#x1f5b #x1f53)
(#x1f5d #x1f55)
(#x1f5f #x1f57)
(#x1f68 #x1f60)
(#x1f69 #x1f61)
(#x1f6a #x1f62)
(#x1f6b #x1f63)
(#x1f6c #x1f64)
(#x1f6d #x1f65)
(#x1f6e #x1f66)
(#x1f6f #x1f67)
(#x1f80 #x1f00 #x03b9)
(#x1f81 #x1f01 #x03b9)
(#x1f82 #x1f02 #x03b9)
(#x1f83 #x1f03 #x03b9)
(#x1f84 #x1f04 #x03b9)
(#x1f85 #x1f05 #x03b9)
(#x1f86 #x1f06 #x03b9)
(#x1f87 #x1f07 #x03b9)
(#x1f88 #x1f00 #x03b9)
(#x1f88 #x1f80)
(#x1f89 #x1f01 #x03b9)
(#x1f89 #x1f81)
(#x1f8a #x1f02 #x03b9)
(#x1f8a #x1f82)
(#x1f8b #x1f03 #x03b9)
(#x1f8b #x1f83)
(#x1f8c #x1f04 #x03b9)
(#x1f8c #x1f84)
(#x1f8d #x1f05 #x03b9)
(#x1f8d #x1f85)
(#x1f8e #x1f06 #x03b9)
(#x1f8e #x1f86)
(#x1f8f #x1f07 #x03b9)
(#x1f8f #x1f87)
(#x1f90 #x1f20 #x03b9)
(#x1f91 #x1f21 #x03b9)
(#x1f92 #x1f22 #x03b9)
(#x1f93 #x1f23 #x03b9)
(#x1f94 #x1f24 #x03b9)
(#x1f95 #x1f25 #x03b9)
(#x1f96 #x1f26 #x03b9)
(#x1f97 #x1f27 #x03b9)
(#x1f98 #x1f20 #x03b9)
(#x1f98 #x1f90)
(#x1f99 #x1f21 #x03b9)
(#x1f99 #x1f91)
(#x1f9a #x1f22 #x03b9)
(#x1f9a #x1f92)
(#x1f9b #x1f23 #x03b9)
(#x1f9b #x1f93)
(#x1f9c #x1f24 #x03b9)
(#x1f9c #x1f94)
(#x1f9d #x1f25 #x03b9)
(#x1f9d #x1f95)
(#x1f9e #x1f26 #x03b9)
(#x1f9e #x1f96)
(#x1f9f #x1f27 #x03b9)
(#x1f9f #x1f97)
(#x1fa0 #x1f60 #x03b9)
(#x1fa1 #x1f61 #x03b9)
(#x1fa2 #x1f62 #x03b9)
(#x1fa3 #x1f63 #x03b9)
(#x1fa4 #x1f64 #x03b9)
(#x1fa5 #x1f65 #x03b9)
(#x1fa6 #x1f66 #x03b9)
(#x1fa7 #x1f67 #x03b9)
(#x1fa8 #x1f60 #x03b9)
(#x1fa8 #x1fa0)
(#x1fa9 #x1f61 #x03b9)
(#x1fa9 #x1fa1)
(#x1faa #x1f62 #x03b9)
(#x1faa #x1fa2)
(#x1fab #x1f63 #x03b9)
(#x1fab #x1fa3)
(#x1fac #x1f64 #x03b9)
(#x1fac #x1fa4)
(#x1fad #x1f65 #x03b9)
(#x1fad #x1fa5)
(#x1fae #x1f66 #x03b9)
(#x1fae #x1fa6)
(#x1faf #x1f67 #x03b9)
(#x1faf #x1fa7)
(#x1fb2 #x1f70 #x03b9)
(#x1fb3 #x03b1 #x03b9)
(#x1fb4 #x03ac #x03b9)
(#x1fb6 #x03b1 #x0342)
(#x1fb7 #x03b1 #x0342 #x03b9)
(#x1fb8 #x1fb0)
(#x1fb9 #x1fb1)
(#x1fba #x1f70)
(#x1fbb #x1f71)
(#x1fbc #x03b1 #x03b9)
(#x1fbc #x1fb3)
(#x1fbe #x03b9)
(#x1fc2 #x1f74 #x03b9)
(#x1fc3 #x03b7 #x03b9)
(#x1fc4 #x03ae #x03b9)
(#x1fc6 #x03b7 #x0342)
(#x1fc7 #x03b7 #x0342 #x03b9)
(#x1fc8 #x1f72)
(#x1fc9 #x1f73)
(#x1fca #x1f74)
(#x1fcb #x1f75)
(#x1fcc #x03b7 #x03b9)
(#x1fcc #x1fc3)
(#x1fd2 #x03b9 #x0308 #x0300)
(#x1fd3 #x03b9 #x0308 #x0301)
(#x1fd6 #x03b9 #x0342)
(#x1fd7 #x03b9 #x0308 #x0342)
(#x1fd8 #x1fd0)
(#x1fd9 #x1fd1)
(#x1fda #x1f76)
(#x1fdb #x1f77)
(#x1fe2 #x03c5 #x0308 #x0300)
(#x1fe3 #x03c5 #x0308 #x0301)
(#x1fe4 #x03c1 #x0313)
(#x1fe6 #x03c5 #x0342)
(#x1fe7 #x03c5 #x0308 #x0342)
(#x1fe8 #x1fe0)
(#x1fe9 #x1fe1)
(#x1fea #x1f7a)
(#x1feb #x1f7b)
(#x1fec #x1fe5)
(#x1ff2 #x1f7c #x03b9)
(#x1ff3 #x03c9 #x03b9)
(#x1ff4 #x03ce #x03b9)
(#x1ff6 #x03c9 #x0342)
(#x1ff7 #x03c9 #x0342 #x03b9)
(#x1ff8 #x1f78)
(#x1ff9 #x1f79)
(#x1ffa #x1f7c)
(#x1ffb #x1f7d)
(#x1ffc #x03c9 #x03b9)
(#x1ffc #x1ff3)
(#x2126 #x03c9)
(#x212a #x006b)
(#x212b #x00e5)
(#x2132 #x214e)
(#x2160 #x2170)
(#x2161 #x2171)
(#x2162 #x2172)
(#x2163 #x2173)
(#x2164 #x2174)
(#x2165 #x2175)
(#x2166 #x2176)
(#x2167 #x2177)
(#x2168 #x2178)
(#x2169 #x2179)
(#x216a #x217a)
(#x216b #x217b)
(#x216c #x217c)
(#x216d #x217d)
(#x216e #x217e)
(#x216f #x217f)
(#x2183 #x2184)
(#x24b6 #x24d0)
(#x24b7 #x24d1)
(#x24b8 #x24d2)
(#x24b9 #x24d3)
(#x24ba #x24d4)
(#x24bb #x24d5)
(#x24bc #x24d6)
(#x24bd #x24d7)
(#x24be #x24d8)
(#x24bf #x24d9)
(#x24c0 #x24da)
(#x24c1 #x24db)
(#x24c2 #x24dc)
(#x24c3 #x24dd)
(#x24c4 #x24de)
(#x24c5 #x24df)
(#x24c6 #x24e0)
(#x24c7 #x24e1)
(#x24c8 #x24e2)
(#x24c9 #x24e3)
(#x24ca #x24e4)
(#x24cb #x24e5)
(#x24cc #x24e6)
(#x24cd #x24e7)
(#x24ce #x24e8)
(#x24cf #x24e9)
(#x2c00 #x2c30)
(#x2c01 #x2c31)
(#x2c02 #x2c32)
(#x2c03 #x2c33)
(#x2c04 #x2c34)
(#x2c05 #x2c35)
(#x2c06 #x2c36)
(#x2c07 #x2c37)
(#x2c08 #x2c38)
(#x2c09 #x2c39)
(#x2c0a #x2c3a)
(#x2c0b #x2c3b)
(#x2c0c #x2c3c)
(#x2c0d #x2c3d)
(#x2c0e #x2c3e)
(#x2c0f #x2c3f)
(#x2c10 #x2c40)
(#x2c11 #x2c41)
(#x2c12 #x2c42)
(#x2c13 #x2c43)
(#x2c14 #x2c44)
(#x2c15 #x2c45)
(#x2c16 #x2c46)
(#x2c17 #x2c47)
(#x2c18 #x2c48)
(#x2c19 #x2c49)
(#x2c1a #x2c4a)
(#x2c1b #x2c4b)
(#x2c1c #x2c4c)
(#x2c1d #x2c4d)
(#x2c1e #x2c4e)
(#x2c1f #x2c4f)
(#x2c20 #x2c50)
(#x2c21 #x2c51)
(#x2c22 #x2c52)
(#x2c23 #x2c53)
(#x2c24 #x2c54)
(#x2c25 #x2c55)
(#x2c26 #x2c56)
(#x2c27 #x2c57)
(#x2c28 #x2c58)
(#x2c29 #x2c59)
(#x2c2a #x2c5a)
(#x2c2b #x2c5b)
(#x2c2c #x2c5c)
(#x2c2d #x2c5d)
(#x2c2e #x2c5e)
(#x2c60 #x2c61)
(#x2c62 #x026b)
(#x2c63 #x1d7d)
(#x2c64 #x027d)
(#x2c67 #x2c68)
(#x2c69 #x2c6a)
(#x2c6b #x2c6c)
(#x2c6d #x0251)
(#x2c6e #x0271)
(#x2c6f #x0250)
(#x2c70 #x0252)
(#x2c72 #x2c73)
(#x2c75 #x2c76)
(#x2c7e #x023f)
(#x2c7f #x0240)
(#x2c80 #x2c81)
(#x2c82 #x2c83)
(#x2c84 #x2c85)
(#x2c86 #x2c87)
(#x2c88 #x2c89)
(#x2c8a #x2c8b)
(#x2c8c #x2c8d)
(#x2c8e #x2c8f)
(#x2c90 #x2c91)
(#x2c92 #x2c93)
(#x2c94 #x2c95)
(#x2c96 #x2c97)
(#x2c98 #x2c99)
(#x2c9a #x2c9b)
(#x2c9c #x2c9d)
(#x2c9e #x2c9f)
(#x2ca0 #x2ca1)
(#x2ca2 #x2ca3)
(#x2ca4 #x2ca5)
(#x2ca6 #x2ca7)
(#x2ca8 #x2ca9)
(#x2caa #x2cab)
(#x2cac #x2cad)
(#x2cae #x2caf)
(#x2cb0 #x2cb1)
(#x2cb2 #x2cb3)
(#x2cb4 #x2cb5)
(#x2cb6 #x2cb7)
(#x2cb8 #x2cb9)
(#x2cba #x2cbb)
(#x2cbc #x2cbd)
(#x2cbe #x2cbf)
(#x2cc0 #x2cc1)
(#x2cc2 #x2cc3)
(#x2cc4 #x2cc5)
(#x2cc6 #x2cc7)
(#x2cc8 #x2cc9)
(#x2cca #x2ccb)
(#x2ccc #x2ccd)
(#x2cce #x2ccf)
(#x2cd0 #x2cd1)
(#x2cd2 #x2cd3)
(#x2cd4 #x2cd5)
(#x2cd6 #x2cd7)
(#x2cd8 #x2cd9)
(#x2cda #x2cdb)
(#x2cdc #x2cdd)
(#x2cde #x2cdf)
(#x2ce0 #x2ce1)
(#x2ce2 #x2ce3)
(#x2ceb #x2cec)
(#x2ced #x2cee)
(#xa640 #xa641)
(#xa642 #xa643)
(#xa644 #xa645)
(#xa646 #xa647)
(#xa648 #xa649)
(#xa64a #xa64b)
(#xa64c #xa64d)
(#xa64e #xa64f)
(#xa650 #xa651)
(#xa652 #xa653)
(#xa654 #xa655)
(#xa656 #xa657)
(#xa658 #xa659)
(#xa65a #xa65b)
(#xa65c #xa65d)
(#xa65e #xa65f)
(#xa660 #xa661)
(#xa662 #xa663)
(#xa664 #xa665)
(#xa666 #xa667)
(#xa668 #xa669)
(#xa66a #xa66b)
(#xa66c #xa66d)
(#xa680 #xa681)
(#xa682 #xa683)
(#xa684 #xa685)
(#xa686 #xa687)
(#xa688 #xa689)
(#xa68a #xa68b)
(#xa68c #xa68d)
(#xa68e #xa68f)
(#xa690 #xa691)
(#xa692 #xa693)
(#xa694 #xa695)
(#xa696 #xa697)
(#xa722 #xa723)
(#xa724 #xa725)
(#xa726 #xa727)
(#xa728 #xa729)
(#xa72a #xa72b)
(#xa72c #xa72d)
(#xa72e #xa72f)
(#xa732 #xa733)
(#xa734 #xa735)
(#xa736 #xa737)
(#xa738 #xa739)
(#xa73a #xa73b)
(#xa73c #xa73d)
(#xa73e #xa73f)
(#xa740 #xa741)
(#xa742 #xa743)
(#xa744 #xa745)
(#xa746 #xa747)
(#xa748 #xa749)
(#xa74a #xa74b)
(#xa74c #xa74d)
(#xa74e #xa74f)
(#xa750 #xa751)
(#xa752 #xa753)
(#xa754 #xa755)
(#xa756 #xa757)
(#xa758 #xa759)
(#xa75a #xa75b)
(#xa75c #xa75d)
(#xa75e #xa75f)
(#xa760 #xa761)
(#xa762 #xa763)
(#xa764 #xa765)
(#xa766 #xa767)
(#xa768 #xa769)
(#xa76a #xa76b)
(#xa76c #xa76d)
(#xa76e #xa76f)
(#xa779 #xa77a)
(#xa77b #xa77c)
(#xa77d #x1d79)
(#xa77e #xa77f)
(#xa780 #xa781)
(#xa782 #xa783)
(#xa784 #xa785)
(#xa786 #xa787)
(#xa78b #xa78c)
(#xa78d #x0265)
(#xa790 #xa791)
(#xa7a0 #xa7a1)
(#xa7a2 #xa7a3)
(#xa7a4 #xa7a5)
(#xa7a6 #xa7a7)
(#xa7a8 #xa7a9)
(#xfb00 #x0066 #x0066)
(#xfb01 #x0066 #x0069)
(#xfb02 #x0066 #x006c)
(#xfb03 #x0066 #x0066 #x0069)
(#xfb04 #x0066 #x0066 #x006c)
(#xfb05 #x0073 #x0074)
(#xfb06 #x0073 #x0074)
(#xfb13 #x0574 #x0576)
(#xfb14 #x0574 #x0565)
(#xfb15 #x0574 #x056b)
(#xfb16 #x057e #x0576)
(#xfb17 #x0574 #x056d)
(#xff21 #xff41)
(#xff22 #xff42)
(#xff23 #xff43)
(#xff24 #xff44)
(#xff25 #xff45)
(#xff26 #xff46)
(#xff27 #xff47)
(#xff28 #xff48)
(#xff29 #xff49)
(#xff2a #xff4a)
(#xff2b #xff4b)
(#xff2c #xff4c)
(#xff2d #xff4d)
(#xff2e #xff4e)
(#xff2f #xff4f)
(#xff30 #xff50)
(#xff31 #xff51)
(#xff32 #xff52)
(#xff33 #xff53)
(#xff34 #xff54)
(#xff35 #xff55)
(#xff36 #xff56)
(#xff37 #xff57)
(#xff38 #xff58)
(#xff39 #xff59)
(#xff3a #xff5a)
(#x10400 #x10428)
(#x10401 #x10429)
(#x10402 #x1042a)
(#x10403 #x1042b)
(#x10404 #x1042c)
(#x10405 #x1042d)
(#x10406 #x1042e)
(#x10407 #x1042f)
(#x10408 #x10430)
(#x10409 #x10431)
(#x1040a #x10432)
(#x1040b #x10433)
(#x1040c #x10434)
(#x1040d #x10435)
(#x1040e #x10436)
(#x1040f #x10437)
(#x10410 #x10438)
(#x10411 #x10439)
(#x10412 #x1043a)
(#x10413 #x1043b)
(#x10414 #x1043c)
(#x10415 #x1043d)
(#x10416 #x1043e)
(#x10417 #x1043f)
(#x10418 #x10440)
(#x10419 #x10441)
(#x1041a #x10442)
(#x1041b #x10443)
(#x1041c #x10444)
(#x1041d #x10445)
(#x1041e #x10446)
(#x1041f #x10447)
(#x10420 #x10448)
(#x10421 #x10449)
(#x10422 #x1044a)
(#x10423 #x1044b)
(#x10424 #x1044c)
(#x10425 #x1044d)
(#x10426 #x1044e)
(#x10427 #x1044f)
))
