#!/usr/bin/env python3
"""Tests of src/math/random.bend and src/crypto/random.bend.

  python3 tools/check_random.py [seed]

Runs build/math/random (tests/math/random.bend) and compares it with

  1. Go's published vectors (Go 1.23+, BSD licence, copied below):
     math/rand/v2 chacha8_test.go chacha8output (372 outputs of ChaCha8 for
     the seed "ABCDEFGHIJKLMNOPQRSTUVWXYZ123456", three key erasures; the
     same list is internal/chacha8rand/rand_test.go's output and C2SP's
     sample), chacha8hash (SHA-256 of 2976 bytes of ChaCha8.Read, in one
     read, in one-byte reads and in random chunks), pcg_test.go TestPCG
     (NewPCG(1, 2)), and regress_test.go's regressGolden for every method
     implemented here (Float64, Int, Int32, Int32N, Int64, Int64N, IntN,
     Perm, Uint32, Uint32N, Uint64, Uint64N, UintN; a fresh NewPCG(1, 2) per
     method, 20 calls each);
  2. a Python mirror of Go's math/rand/v2 (rand.go, pcg.go) and of the C2SP
     chacha8rand pseudocode (written from the specification, not from the
     Bend code), on random keys and seeds with random call sequences and the
     edge bounds of uint64n (1, powers of two, 2^32 +- 1, 2^63 + 1, where
     almost half the draws are rejected, 2^64 - 1 and 0, read as 2^64);
  3. a chi-square test of uint64n's buckets (smoke test of uniformity: the
     exact unbiasedness is proved, proofs/math/random/lemire.bend).

Prints a JSON verdict; exit status 1 on any mismatch.
"""
import hashlib, json, math, random, struct, subprocess, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
BIN = ROOT / 'build/math/random'
M32 = (1 << 32) - 1
M64 = (1 << 64) - 1
SEED = b'ABCDEFGHIJKLMNOPQRSTUVWXYZ123456'
CHACHA8_HASH = 'bfec3d418b829afe5df2d8887d1508348409c293b73758d7efd841dd995fe021'
PCG_12 = [0xc4f5a58656eef510, 0x9dcec3ad077dec6c, 0xc8d04605312f8088, 0xcbedc0dcb63ac19a,
          0x3bf98798cae97950, 0xa8c6d7f8d485abc, 0x7ffa3780429cd279, 0x730ad2626b1c2f8e,
          0x21ff2330f4a0ad99, 0x2f0901a1947094b0, 0xa9735a3cfbe36cef, 0x71ddb0a01a12c84a,
          0xf0e53e77a78453bb, 0x1f173e9663be1e9d, 0x657651da3ac4115e, 0xc8987376b65a157b,
          0xbb17008f5fca28e7, 0x8232bd645f29ed22, 0x12be8f07ad14c539, 0x54908a48e8e4736e]
# math/rand/v2 chacha8_test.go chacha8output
CHACHA8_OUTPUT = [
    0xb773b6063d4616a5, 0x1160af22a66abc3c, 0x8c2599d9418d287c, 0x7ee07e037edc5cd6,
    0xcfaa9ee02d1c16ad, 0x0e090eef8febea79, 0x3c82d271128b5b3e, 0x9c5addc11252a34f,
    0xdf79bb617d6ceea6, 0x36d553591f9d736a, 0xeef0d14e181ee01f, 0x089bfc760ae58436,
    0xd9e52b59cc2ad268, 0xeb2fb4444b1b8aba, 0x4f95c8a692c46661, 0xc3c6323217cae62c,
    0x91ebb4367f4e2e7e, 0x784cf2c6a0ec9bc6, 0x5c34ec5c34eabe20, 0x4f0a8f515570daa8,
    0xfc35dcb4113d6bf2, 0x5b0da44c645554bc, 0x6d963da3db21d9e1, 0xeeaefc3150e500f3,
    0x2d37923dda3750a5, 0x380d7a626d4bc8b0, 0xeeaf68ede3d7ee49, 0xf4356695883b717c,
    0x846a9021392495a4, 0x8e8510549630a61b, 0x18dc02545dbae493, 0x0f8f9ff0a65a3d43,
    0xccf065f7190ff080, 0xfd76d1aa39673330, 0x95d232936cba6433, 0x6c7456d1070cbd17,
    0x462acfdaff8c6562, 0x5bafab866d34fc6a, 0x0c862f78030a2988, 0xd39a83e407c3163d,
    0xc00a2b7b45f22ebf, 0x564307c62466b1a9, 0x257e0424b0c072d4, 0x6fb55e99496c28fe,
    0xae9873a88f5cd4e0, 0x4657362ac60d3773, 0x1c83f91ecdf23e8e, 0x6fdc0792c15387c0,
    0x36dad2a30dfd2b5c, 0xa4b593290595bdb7, 0x4de18934e4cc02c5, 0xcdc0d604f015e3a7,
    0xfba0dbf69ad80321, 0x60e8bea3d139de87, 0xd18a4d851ef48756, 0x6366447c2215f34a,
    0x05682e97d3d007ee, 0x4c0e8978c6d54ab2, 0xcf1e9f6a6712edc2, 0x061439414c80cfd3,
    0xd1a8b6e2745c0ead, 0x31a7918d45c410e8, 0xabcc61ad90216eec, 0x4040d92d2032a71a,
    0x3cd2f66ffb40cd68, 0xdcd051c07295857a, 0xeab55cbcd9ab527e, 0x18471dce781bdaac,
    0xf7f08cd144dc7252, 0x5804e0b13d7f40d1, 0x5cb1a446e4b2d35b, 0xe6d4a728d2138a06,
    0x05223e40ca60dad8, 0x2d61ec3206ac6a68, 0xab692356874c17b8, 0xc30954417676de1c,
    0x4f1ace3732225624, 0xfba9510813988338, 0x997f200f52752e11, 0x1116aaafe86221fa,
    0x07ce3b5cb2a13519, 0x2956bc72bc458314, 0x4188b7926140eb78, 0x56ca6dbfd4adea4d,
    0x7fe3c22349340ce5, 0x35c08f9c37675f8a, 0x11e1c7fbef5ed521, 0x98adc8464ec1bc75,
    0xd163b2c73d1203f8, 0x8c761ee043a2f3f3, 0x24b99d6accecd7b7, 0x793e31aa112f0370,
    0x8e87dc2a19285139, 0x4247ae04f7096e25, 0x514f3122926fe20f, 0xdc6fb3f045d2a7e9,
    0x15cb30cecdd18eba, 0xcbc7fdecf6900274, 0x3fb5c696dc8ba021, 0xd1664417c8d274e6,
    0x05f7e445ea457278, 0xf920bbca1b9db657, 0x0c1950b4da22cb99, 0xf875baf1af09e292,
    0xbed3d7b84250f838, 0xf198e8080fd74160, 0xc9eda51d9b7ea703, 0xf709ef55439bf8f6,
    0xd20c74feebf116fc, 0x305668eb146d7546, 0x829af3ec10d89787, 0x15b8f9697b551dbc,
    0xfc823c6c8e64b8c9, 0x345585e8183b40bc, 0x674b4171d6581368, 0x1234d81cd670e9f7,
    0x0e505210d8a55e19, 0xe8258d69eeeca0dc, 0x05d4c452e8baf67e, 0xe8dbe30116a45599,
    0x1cf08ce1b1176f00, 0xccf7d0a4b81ecb49, 0x303fea136b2c430e, 0x861d6c139c06c871,
    0x5f41df72e05e0487, 0x25bd7e1e1ae26b1d, 0xbe9f4004d662a41d, 0x65bf58d483188546,
    0xd1b27cff69db13cc, 0x01a6663372c1bb36, 0x578dd7577b727f4d, 0x19c78f066c083cf6,
    0xdbe014d4f9c391bb, 0x97fbb2dd1d13ffb3, 0x31c91e0af9ef8d4f, 0x094dfc98402a43ba,
    0x069bd61bea37b752, 0x5b72d762e8d986ca, 0x72ee31865904bc85, 0xd1f5fdc5cd36c33e,
    0xba9b4980a8947cad, 0xece8f05eac49ab43, 0x65fe1184abae38e7, 0x2d7cb9dea5d31452,
    0xcc71489476e467e3, 0x4c03a258a578c68c, 0x00efdf9ecb0fd8fc, 0x9924cad471e2666d,
    0x87f8668318f765e9, 0xcb4dc57c1b55f5d8, 0xd373835a86604859, 0xe526568b5540e482,
    0x1f39040f08586fec, 0xb764f3f00293f8e6, 0x049443a2f6bd50a8, 0x76fec88697d3941a,
    0x3efb70d039bae7a2, 0xe2f4611368eca8a8, 0x7c007a96e01d2425, 0xbbcce5768e69c5bf,
    0x784fb4985c42aac3, 0xf72b5091aa223874, 0x3630333fb1e62e07, 0x8e7319ebdebbb8de,
    0x2a3982bca959fa00, 0xb2b98b9f964ba9b3, 0xf7e31014adb71951, 0xebd0fca3703acc82,
    0xec654e2a2fe6419a, 0xb326132d55a52e2c, 0x2248c57f44502978, 0x32710c2f342daf16,
    0x0517b47b5acb2bec, 0x4c7a718fca270937, 0xd69142bed0bcc541, 0xe40ebcb8ff52ce88,
    0x3e44a2dbc9f828d4, 0xc74c2f4f8f873f58, 0x3dbf648eb799e45b, 0x33f22475ee0e86f8,
    0x1eb4f9ee16d47f65, 0x40f8d2b8712744e3, 0xb886b4da3cb14572, 0x2086326fbdd6f64d,
    0xcc3de5907dd882b9, 0xa2e8b49a5ee909df, 0xdbfb8e7823964c10, 0x70dd6089ef0df8d5,
    0x30141663cdd9c99f, 0x04b805325c240365, 0x7483d80314ac12d6, 0x2b271cb91aa7f5f9,
    0x97e2245362abddf0, 0x5a84f614232a9fab, 0xf71125fcda4b7fa2, 0x1ca5a61d74b27267,
    0x38cc6a9b3adbcb45, 0xdde1bb85dc653e39, 0xe9d0c8fa64f89fd4, 0x02c5fb1ecd2b4188,
    0xf2bd137bca5756e5, 0xadefe25d121be155, 0x56cd1c3c5d893a8e, 0x4c50d337beb65bb9,
    0x918c5151675cf567, 0xaba649ffcfb56a1e, 0x20c74ab26a2247cd, 0x71166bac853c08da,
    0xb07befe2e584fc5d, 0xda45ff2a588dbf32, 0xdb98b03c4d75095e, 0x60285ae1aaa65a4c,
    0xf93b686a263140b8, 0xde469752ee1c180e, 0xcec232dc04129aae, 0xeb916baa1835ea04,
    0xd49c21c8b64388ff, 0x72a82d9658864888, 0x003348ef7eac66a8, 0x7f6f67e655b209eb,
    0x532ffb0b7a941b25, 0xd940ade6128deede, 0xdf24f2a1af89fe23, 0x95aa3b4988195ae0,
    0x3da649404f94be4a, 0x692dad132c3f7e27, 0x40aee76ecaaa9eb8, 0x1294a01e09655024,
    0x6df797abdba4e4f5, 0xea2fb6024c1d7032, 0x5f4e0492295489fc, 0x57972914ea22e06a,
    0x9a8137d133aad473, 0xa2e6dd6ae7cdf2f3, 0x9f42644f18086647, 0x16d03301c170bd3e,
    0x908c416fa546656d, 0xe081503be22e123e, 0x077cf09116c4cc72, 0xcbd25cd264b7f229,
    0x3db2f468ec594031, 0x46c00e734c9badd5, 0xd0ec0ac72075d861, 0x3037cb3cf80b7630,
    0x574c3d7b3a2721c6, 0xae99906a0076824b, 0xb175a5418b532e70, 0xd8b3e251ee231ddd,
    0xb433eec25dca1966, 0x530f30dc5cff9a93, 0x9ff03d98b53cd335, 0xafc4225076558cdf,
    0xef81d3a28284402a, 0x110bdbf51c110a28, 0x9ae1b255d027e8f6, 0x7de3e0aa24688332,
    0xe483c3ecd2067ee2, 0xf829328b276137e6, 0xa413ccad57562cad, 0xe6118e8b496acb1f,
    0x8288dca6da5ec01f, 0xa53777dc88c17255, 0x8a00f1e0d5716eda, 0x618e6f47b7a720a8,
    0x9e3907b0c692a841, 0x978b42ca963f34f3, 0x75e4b0cd98a7d7ef, 0xde4dbd6e0b5f4752,
    0x0252e4153f34493f, 0x50f0e7d803734ef9, 0x237766a38ed167ee, 0x4124414001ee39a0,
    0xd08df643e535bb21, 0x34f575b5a9a80b74, 0x2c343af87297f755, 0xcd8b6d99d821f7cb,
    0xe376fd7256fc48ae, 0xe1b06e7334352885, 0xfa87b26f86c169eb, 0x36c1604665a971de,
    0xdba147c2239c8e80, 0x6b208e69fc7f0e24, 0x8795395b6f2b60c3, 0x05dabee9194907f4,
    0xb98175142f5ed902, 0x5e1701e2021ddc81, 0x0875aba2755eed08, 0x778d83289251de95,
    0x3bfbe46a039ecb31, 0xb24704fce4cbd7f9, 0x6985ffe9a7c91e3d, 0xc8efb13df249dabb,
    0xb1037e64b0f4c9f6, 0x55f69fd197d6b7c3, 0x672589d71d68a90c, 0xbebdb8224f50a77e,
    0x3f589f80007374a7, 0xd307f4635954182a, 0xcff5850c10d4fd90, 0xc6da02dfb6408e15,
    0x93daeef1e2b1a485, 0x65d833208aeea625, 0xe2b13fa13ed3b5fa, 0x67053538130fb68e,
    0xc1042f6598218fa9, 0xee5badca749b8a2e, 0x6d22a3f947dae37d, 0xb62c6d1657f4dbaf,
    0x6e007de69704c20b, 0x1af2b913fc3841d8, 0xdc0e47348e2e8e22, 0x9b1ddef1cf958b22,
    0x632ed6b0233066b8, 0xddd02d3311bed8f2, 0xf147cfe1834656e9, 0x399aaa49d511597a,
    0x6b14886979ec0309, 0x64fc4ac36b5afb97, 0xb82f78e07f7cf081, 0x10925c9a323d0e1b,
    0xf451c79ee13c63f6, 0x7c2fc180317876c7, 0x35a12bd9eecb7d22, 0x335654a539621f90,
    0xcc32a3f35db581f0, 0xc60748a80b2369cb, 0x7c4dd3b08591156b, 0xac1ced4b6de22291,
    0xa32cfa2df134def5, 0x627108918dea2a53, 0x0555b1608fcb4ff4, 0x143ee7ac43aaa33c,
    0xdae90ce7cf4fc218, 0x4d68fc2582bcf4b5, 0x37094e1849135d71, 0xf7857e09f3d49fd8,
    0x007538c503768be7, 0xedf648ba2f6be601, 0xaa347664dd72513e, 0xbe63893c6ef23b86,
    0x130b85710605af97, 0xdd765c6b1ef6ab56, 0xf3249a629a97dc6b, 0x2a114f9020fab8e5,
    0x5a69e027cfc6ad08, 0x3c4ccb36f1a5e050, 0x2e9e7d596834f0a5, 0x2430be6858fce789,
    0xe90b862f2466e597, 0x895e2884f159a9ec, 0x26ab8fa4902fcb57, 0xa6efff5c54e1fa50,
    0x333ac4e5811a8255, 0xa58d515f02498611, 0xfe5a09dcb25c6ef4, 0x03898988ab5f5818,
    0x289ff6242af6c617, 0x3d9dd59fd381ea23, 0x52d7d93d8a8aae51, 0xc76a123d511f786f,
    0xf68901edaf00c46c, 0x8c630871b590de80, 0x05209c308991e091, 0x1f809f99b4788177,
    0x11170c2eb6c19fd8, 0x44433c779062ba58, 0xc0acb51af1874c45, 0x9f2e134284809fa1,
    0xedb523bd15c619fa, 0x02d97fd53ecc23c0, 0xacaf05a34462374c, 0xddd9c6d34bffa11f,
]
# math/rand/v2 regress_test.go regressGolden (argument, value) per method
GOLDEN = {
    'Float64': [(None, 0.6764556596678251), (None, 0.4613862177205994), (None, 0.5085473976760264), (None, 0.4297927436037299), (None, 0.797802349388613), (None, 0.3883664855410056), (None, 0.8192750264193612), (None, 0.3381816951746133), (None, 0.9730458047755973), (None, 0.281449117585586), (None, 0.6047654075331631), (None, 0.9278107175107462), (None, 0.16387541502137226), (None, 0.7263900707339023), (None, 0.6974917552729882), (None, 0.7640946923790318), (None, 0.7188183661358182), (None, 0.5856191500346635), (None, 0.9549597149363428), (None, 0.5168804691962643)],
    'Int': [(None, 4969059760275911952), (None, 2147869220224756844), (None, 5246770554000605320), (None, 5471241176507662746), (None, 4321634407747778896), (None, 760102831717374652), (None, 9221744211007427193), (None, 8289669384274456462), (None, 2449715415482412441), (None, 3389241988064777392), (None, 2986830195847294191), (None, 8204908297817606218), (None, 8134976985547166651), (None, 2240328155279531677), (None, 7311121042813227358), (None, 5231057920893523323), (None, 4257872588489500903), (None, 158397175702351138), (None, 1350674201389090105), (None, 6093522341581845358)],
    'Int32': [(None, 1652216515), (None, 1323786710), (None, 1684546306), (None, 1710678126), (None, 503104460), (None, 88487615), (None, 1073552320), (None, 965044529), (None, 285184408), (None, 394559696), (None, 1421454622), (None, 955177040), (None, 2020777787), (None, 260808523), (None, 851126509), (None, 1682717115), (None, 1569423431), (None, 1092181682), (None, 157239171), (None, 709379364)],
    'Int32N': [('1', 0), ('10', 6), ('32', 8), ('1048576', 704922), ('1048577', 245656), ('1000000000', 41205257), ('1073741824', 43831929), ('2147483646', 965044528), ('2147483647', 285184408), ('1', 0), ('10', 6), ('32', 10), ('1048576', 283579), ('1048577', 127348), ('1000000000', 396336665), ('1073741824', 911873403), ('2147483646', 1569423430), ('2147483647', 1092181681), ('1', 0), ('10', 3)],
    'Int64': [(None, 4969059760275911952), (None, 2147869220224756844), (None, 5246770554000605320), (None, 5471241176507662746), (None, 4321634407747778896), (None, 760102831717374652), (None, 9221744211007427193), (None, 8289669384274456462), (None, 2449715415482412441), (None, 3389241988064777392), (None, 2986830195847294191), (None, 8204908297817606218), (None, 8134976985547166651), (None, 2240328155279531677), (None, 7311121042813227358), (None, 5231057920893523323), (None, 4257872588489500903), (None, 158397175702351138), (None, 1350674201389090105), (None, 6093522341581845358)],
    'Int64N': [('1', 0), ('10', 6), ('32', 8), ('1048576', 704922), ('1048577', 245656), ('1000000000', 41205257), ('1073741824', 43831929), ('2147483646', 965044528), ('2147483647', 285184408), ('1000000000000000000', 183731176326946086), ('1152921504606846976', 680987186633600239), ('9223372036854775806', 4102454148908803108), ('9223372036854775807', 8679174511200971228), ('1', 0), ('10', 3), ('32', 27), ('1048576', 665831), ('1048577', 533292), ('1000000000', 73220195), ('1073741824', 686060398)],
    'IntN': [('1', 0), ('10', 6), ('32', 8), ('1048576', 704922), ('1048577', 245656), ('1000000000', 41205257), ('1073741824', 43831929), ('2147483646', 965044528), ('2147483647', 285184408), ('1000000000000000000', 183731176326946086), ('1152921504606846976', 680987186633600239), ('9223372036854775806', 4102454148908803108), ('9223372036854775807', 8679174511200971228), ('1', 0), ('10', 3), ('32', 27), ('1048576', 665831), ('1048577', 533292), ('1000000000', 73220195), ('1073741824', 686060398)],
    'Perm': [('0', []), ('1', [0]), ('5', [1, 4, 2, 0, 3]), ('8', [4, 3, 6, 1, 5, 2, 7, 0]), ('9', [6, 5, 1, 8, 7, 2, 0, 3, 4]), ('10', [9, 4, 2, 5, 6, 8, 1, 7, 0, 3]), ('16', [5, 9, 3, 1, 4, 2, 10, 7, 15, 11, 0, 14, 13, 8, 6, 12]), ('0', []), ('1', [0]), ('5', [4, 2, 1, 3, 0]), ('8', [0, 2, 3, 1, 5, 4, 6, 7]), ('9', [2, 0, 8, 3, 4, 7, 6, 5, 1]), ('10', [0, 6, 5, 3, 8, 4, 1, 2, 9, 7]), ('16', [9, 14, 4, 11, 13, 8, 0, 6, 2, 12, 3, 7, 1, 10, 5, 15]), ('0', []), ('1', [0]), ('5', [2, 4, 0, 3, 1]), ('8', [3, 2, 1, 0, 7, 5, 4, 6]), ('9', [1, 3, 4, 5, 0, 2, 7, 8, 6]), ('10', [1, 8, 4, 7, 2, 6, 5, 9, 0, 3])],
    'Uint32': [(None, 3304433030), (None, 2647573421), (None, 3369092613), (None, 3421356252), (None, 1006208920), (None, 176975231), (None, 2147104640), (None, 1930089058), (None, 570368816), (None, 789119393), (None, 2842909244), (None, 1910354080), (None, 4041555575), (None, 521617046), (None, 1702253018), (None, 3365434230), (None, 3138846863), (None, 2184363364), (None, 314478343), (None, 1418758728)],
    'Uint32N': [('1', 0), ('10', 6), ('32', 8), ('1048576', 704922), ('1048577', 245656), ('1000000000', 41205257), ('1073741824', 43831929), ('2147483646', 965044528), ('2147483647', 285184408), ('4294967294', 789119393), ('4294967295', 2842909244), ('1', 0), ('10', 9), ('32', 29), ('1048576', 266590), ('1048577', 821640), ('1000000000', 730819735), ('1073741824', 522841378), ('2147483646', 157239171), ('2147483647', 709379364)],
    'Uint64': [(None, 14192431797130687760), (None, 11371241257079532652), (None, 14470142590855381128), (None, 14694613213362438554), (None, 4321634407747778896), (None, 760102831717374652), (None, 9221744211007427193), (None, 8289669384274456462), (None, 2449715415482412441), (None, 3389241988064777392), (None, 12210202232702069999), (None, 8204908297817606218), (None, 17358349022401942459), (None, 2240328155279531677), (None, 7311121042813227358), (None, 14454429957748299131), (None, 13481244625344276711), (None, 9381769212557126946), (None, 1350674201389090105), (None, 6093522341581845358)],
    'Uint64N': [('1', 0), ('10', 6), ('32', 8), ('1048576', 704922), ('1048577', 245656), ('1000000000', 41205257), ('1073741824', 43831929), ('2147483646', 965044528), ('2147483647', 285184408), ('1000000000000000000', 183731176326946086), ('1152921504606846976', 680987186633600239), ('9223372036854775806', 4102454148908803108), ('9223372036854775807', 8679174511200971228), ('18446744073709551614', 2240328155279531676), ('18446744073709551615', 7311121042813227357), ('1', 0), ('10', 7), ('32', 2), ('1048576', 312633), ('1048577', 346376)],
    'UintN': [('1', 0), ('10', 6), ('32', 8), ('1048576', 704922), ('1048577', 245656), ('1000000000', 41205257), ('1073741824', 43831929), ('2147483646', 965044528), ('2147483647', 285184408), ('1000000000000000000', 183731176326946086), ('1152921504606846976', 680987186633600239), ('9223372036854775806', 4102454148908803108), ('9223372036854775807', 8679174511200971228), ('18446744073709551614', 2240328155279531676), ('18446744073709551615', 7311121042813227357), ('1', 0), ('10', 7), ('32', 2), ('1048576', 312633), ('1048577', 346376)],
}


# ---------------------------------------------------------------- the mirror

def rotl(x, n):
    return ((x << n) | (x >> (32 - n))) & M32


def quarter(s, a, b, c, d):
    s[a] = (s[a] + s[b]) & M32; s[d] = rotl(s[d] ^ s[a], 16)
    s[c] = (s[c] + s[d]) & M32; s[b] = rotl(s[b] ^ s[c], 12)
    s[a] = (s[a] + s[b]) & M32; s[d] = rotl(s[d] ^ s[a], 8)
    s[c] = (s[c] + s[d]) & M32; s[b] = rotl(s[b] ^ s[c], 7)


CONSTANTS = [0x61707865, 0x3320646E, 0x79622D32, 0x6B206574]


def chacha8_block(key, counter):
    """RFC 8439's block function with 8 rounds and a zero nonce, as words."""
    init = CONSTANTS + list(key) + [counter, 0, 0, 0]
    s = init[:]
    for _ in range(4):
        for q in [(0, 4, 8, 12), (1, 5, 9, 13), (2, 6, 10, 14), (3, 7, 11, 15),
                  (0, 5, 10, 15), (1, 6, 11, 12), (2, 7, 8, 13), (3, 4, 9, 14)]:
            quarter(s, *q)
    return [(s[i] + init[i]) & M32 for i in range(16)]


def c2sp_iteration(key):
    """C2SP chacha8rand: 1024 bytes (as 256 words) of one iteration."""
    stream = []
    for i in range(16):
        w = chacha8_block(key, i)
        for j in range(4):
            w[j] = (w[j] - CONSTANTS[j]) & M32
        w[12] = (w[12] - i) & M32
        stream += w
    out = []
    for g in range(4):
        blocks = stream[64 * g:64 * g + 64]
        for i in range(16):
            for b in range(4):
                out.append(blocks[16 * b + i])
    return out[:248], out[248:]


def words_of(seed_bytes):
    return [int.from_bytes(seed_bytes[4 * i:4 * i + 4], 'little') for i in range(8)]


class ChaCha8:
    def __init__(self, key):
        self.key = list(key)
        self.buf = []

    def next(self):
        if not self.buf:
            out, self.key = c2sp_iteration(self.key)
            self.buf = [out[2 * i] | out[2 * i + 1] << 32 for i in range(124)]
        return self.buf.pop(0)


class PCG:
    MUL = (2549297995355413924 << 64) | 4865540595714422341
    INC = (6364136223846793005 << 64) | 1442695040888963407

    def __init__(self, s1, s2):
        self.state = (s1 << 64) | s2

    def next(self):
        self.state = (self.state * self.MUL + self.INC) & ((1 << 128) - 1)
        hi, lo = self.state >> 64, self.state & M64
        hi ^= hi >> 32
        hi = (hi * 0xda942042e4dd58b5) & M64
        hi ^= hi >> 48
        return (hi * (lo | 1)) & M64


class Rand:
    """Go's math/rand/v2 Rand over a source (64-bit code paths)."""

    def __init__(self, src):
        self.src = src
        self.pending = []

    def uint64(self):
        return self.src.next()

    def uint64n(self, n):
        if n & (n - 1) & M64 == 0:
            return self.uint64() & ((n - 1) & M64)
        m = self.uint64() * n
        hi, lo = m >> 64, m & M64
        if lo < n:
            thresh = ((1 << 64) - n) % n
            while lo < thresh:
                m = self.uint64() * n
                hi, lo = m >> 64, m & M64
        return hi

    def shuffle(self, xs):
        for i in range(len(xs) - 1, 0, -1):
            j = self.uint64n(i + 1)
            xs[i], xs[j] = xs[j], xs[i]
        return xs

    def float64_bits(self):
        return struct.unpack('<Q', struct.pack('<d', (self.uint64() & ((1 << 53) - 1)) / 2.0 ** 53))[0]

    def read(self, n):
        out = []
        while len(out) < n:
            if not self.pending:
                self.pending = list(self.uint64().to_bytes(8, 'little'))
            out.append(self.pending.pop(0))
        return out

    def call(self, tok):
        p = tok.split(':')
        op = p[0]
        if op == 'u64':
            return u64s(self.uint64())
        if op == 'u32':
            return str(self.uint64() >> 32)
        if op == 'i64':
            return u64s(self.uint64() & ((1 << 63) - 1))
        if op == 'i32':
            return str(self.uint64() >> 33)
        if op == 'n':
            return u64s(self.uint64n(u64r(p[1])))
        if op == 'm':
            return str(self.uint64n(int(p[1])) & M32)
        if op == 'i':
            n = int(p[1])
            return str(self.uint64n(n) if n else 0)
        if op == 'r':
            lo, hi = int(p[1]), int(p[2])
            n = max(hi - lo, 0)
            return str(lo + (self.uint64n(n) if n else 0))
        if op == 'f':
            return u64s(self.float64_bits())
        if op == 'p':
            return ','.join(map(str, self.shuffle(list(range(int(p[1]))))))
        if op == 's':
            return ','.join(map(str, self.shuffle(list(range(100, 100 + int(p[1]))))))
        if op == 'b':
            return ','.join(map(str, self.read(int(p[1]))))
        if op == 'c':
            cs = [0] * int(p[1])
            for _ in range(int(p[2])):
                cs[self.uint64n(int(p[1]))] += 1
            return ','.join(map(str, cs))
        raise ValueError(tok)


def u64s(x):
    return '%d_%d' % (x >> 32, x & M32)


def u64r(s):
    h, l = s.split('_')
    return int(h) << 32 | int(l)


# ---------------------------------------------------------------- runner

FAILURES = []
COUNTS = {}


def run(source, toks):
    p = subprocess.run([str(BIN), '--threads', '1', '--', source] + list(toks),
                       capture_output=True, text=True, timeout=1800)
    if p.returncode != 0:
        raise RuntimeError('driver failed on %s: %s' % (source, p.stderr[-300:]))
    return p.stdout.splitlines()


def check(name, got, want):
    COUNTS[name] = COUNTS.get(name, 0) + 1
    if got != want:
        FAILURES.append({'test': name, 'got': str(got)[:300], 'want': str(want)[:300]})


def source_token(kind, key=None, s1=0, s2=0, seed=None):
    if kind in ('c8', 'cr'):
        return kind + ':' + ':'.join(map(str, key))
    if kind in ('c8b', 'crb'):
        return kind + ':' + ':'.join(map(str, seed))
    return 'pcg:%s:%s' % (u64s(s1), u64s(s2))


def mirror(kind, key=None, s1=0, s2=0, seed=None):
    if kind in ('c8', 'cr'):
        return Rand(ChaCha8(key))
    if kind in ('c8b', 'crb'):
        return Rand(ChaCha8(words_of(bytes(seed))))
    return Rand(PCG(s1, s2))


def differential(name, kind, toks, **kw):
    got = run(source_token(kind, **kw), toks)
    r = mirror(kind, **kw)
    want = [r.call(t) for t in toks]
    for i, (g, w) in enumerate(zip(got, want)):
        if g != w:
            check('%s[%d] %s' % (name, i, toks[i]), g, w)
            return
    check(name, len(got), len(want))


# ---------------------------------------------------------------- tests

def go_vectors():
    # the Python mirror itself against Go
    r = ChaCha8(words_of(SEED))
    check('mirror chacha8output', [r.next() for _ in range(372)], CHACHA8_OUTPUT)
    p = PCG(1, 2)
    check('mirror TestPCG', [p.next() for _ in range(20)], PCG_12)
    # ChaCha8, seeded by bytes (and by words)
    got = run(source_token('c8b', seed=list(SEED)), ['u64'] * 372)
    check('go ChaCha8 chacha8output', [u64r(x) for x in got], CHACHA8_OUTPUT)
    got = run(source_token('c8', key=words_of(SEED)), ['u64'] * 372)
    check('go ChaCha8 chacha8output (key words)', [u64r(x) for x in got], CHACHA8_OUTPUT)
    # crypto/random bytes: Go's TestChaCha8Read transcripts
    got = run(source_token('crb', seed=list(SEED)), ['b:2976'])
    check('go ChaCha8.Read one read', hashlib.sha256(bytes(map(int, got[0].split(',')))).hexdigest(), CHACHA8_HASH)
    chunks, n, rng = [], 0, random.Random(5)
    while n < 2976:
        k = min(rng.randrange(100), 2976 - n)
        chunks.append(k)
        n += k
    got = run(source_token('crb', seed=list(SEED)), ['b:%d' % k for k in chunks])
    data = bytes(int(b) for line in got for b in line.split(',') if b != '')
    check('go ChaCha8.Read random chunks', hashlib.sha256(data).hexdigest(), CHACHA8_HASH)
    got = run(source_token('crb', seed=list(SEED)), ['b:1'] * 400)
    r = Rand(ChaCha8(words_of(SEED)))
    check('go ChaCha8.Read one-byte reads (prefix)', [int(x) for x in got], r.read(400))
    # PCG
    got = run(source_token('pcg', s1=1, s2=2), ['u64'] * 20)
    check('go TestPCG', [u64r(x) for x in got], PCG_12)
    # regressGolden: a fresh NewPCG(1, 2) per method
    ops = {
        'Float64': lambda a: 'f', 'Int': lambda a: 'i64', 'Int64': lambda a: 'i64',
        'Int32': lambda a: 'i32', 'Uint32': lambda a: 'u32', 'Uint64': lambda a: 'u64',
        'Int32N': lambda a: 'n:' + u64s(int(a)), 'Int64N': lambda a: 'n:' + u64s(int(a)),
        'Uint64N': lambda a: 'n:' + u64s(int(a)), 'UintN': lambda a: 'n:' + u64s(int(a)),
        'Uint32N': lambda a: 'm:' + a,
        'IntN': lambda a: ('i:' + a) if int(a) < (1 << 48) else ('n:' + u64s(int(a))),
        'Perm': lambda a: 'p:' + a,
    }
    for method, rows in GOLDEN.items():
        toks = [ops[method](a) for a, v in rows]
        got = run(source_token('pcg', s1=1, s2=2), toks)
        for (a, want), g, t in zip(rows, got, toks):
            if method == 'Float64':
                val = struct.unpack('<d', struct.pack('<Q', u64r(g)))[0]
            elif method == 'Perm':
                val = [int(x) for x in g.split(',')] if g else []
            elif t.startswith(('u64', 'i64', 'n:')):
                val = u64r(g)
            else:
                val = int(g)
            check('go regress %s(%s)' % (method, a or ''), val, want)


EDGE = [1, 2, 3, 5, 7, 10, 64, 1000, (1 << 31) - 1, 1 << 31, (1 << 32) - 1, 1 << 32, (1 << 32) + 1,
        (1 << 48) - 1, (1 << 62) + 1, 1 << 63, (1 << 63) + 1, (1 << 63) + 12345, M64 - 1, M64, 0]


def random_toks(rng, k):
    toks = []
    for _ in range(k):
        c = rng.randrange(13)
        if c == 0:
            toks.append(rng.choice(['u64', 'u32', 'i64', 'i32', 'f']))
        elif c <= 5:
            n = rng.choice(EDGE) if rng.random() < 0.5 else rng.randrange(1 << rng.randrange(1, 65))
            toks.append('n:' + u64s(n))
        elif c == 6:
            toks.append('m:%d' % rng.choice([1, 2, 3, 10, (1 << 32) - 1, rng.randrange(1, 1 << 32)]))
        elif c == 7:
            toks.append('i:%d' % rng.choice([0, 1, 6, 1 << 20, (1 << 48) - 1, rng.randrange(1, 1 << 48)]))
        elif c == 8:
            lo = rng.randrange(1 << 40)
            toks.append('r:%d:%d' % (lo, lo + rng.choice([0, 1, 2, 1000, rng.randrange(1 << 40)])))
        elif c == 9:
            toks.append('p:%d' % rng.randrange(0, 40))
        elif c == 10:
            toks.append('s:%d' % rng.randrange(0, 40))
        else:
            toks.append('f')
    return toks


def differentials(seed):
    rng = random.Random(seed)
    for t in range(6):
        key = [rng.randrange(1 << 32) for _ in range(8)]
        differential('chacha8 key %d' % t, 'c8', random_toks(rng, 300), key=key)
    for t in range(3):
        seed_bytes = [rng.randrange(256) for _ in range(32)]
        differential('chacha8 seed %d' % t, 'c8b', random_toks(rng, 300), seed=seed_bytes)
    for t in range(6):
        differential('pcg %d' % t, 'pcg', random_toks(rng, 300), s1=rng.randrange(1 << 64), s2=rng.randrange(1 << 64))
    differential('pcg zero', 'pcg', random_toks(rng, 300), s1=0, s2=0)
    for t in range(4):
        key = [rng.randrange(1 << 32) for _ in range(8)]
        toks = [rng.choice(['b:%d' % rng.randrange(0, 20), 'u64', 'n:' + u64s(rng.choice(EDGE))]) for _ in range(300)]
        differential('crypto key %d' % t, 'cr', toks, key=key)
    # a long ChaCha8 run through many key erasures
    key = [rng.randrange(1 << 32) for _ in range(8)]
    differential('chacha8 long', 'c8', ['u64'] * 399 + ['n:' + u64s((1 << 63) + 1)], key=key)
    # seeds that are not 32 bytes < 256
    for bad in [list(range(31)), list(range(33)), [256] + list(range(31))]:
        got = run('c8b:' + ':'.join(map(str, bad)), ['u64'])
        check('c8b rejects %d bytes, max %d' % (len(bad), max(bad)), got, ['bad seed'])
        got = run('crb:' + ':'.join(map(str, bad)), ['u64'])
        check('crb rejects %d bytes, max %d' % (len(bad), max(bad)), got, ['bad seed'])


def chi_critical(df, z=4.753):
    # Wilson-Hilferty: the upper quantile of chi-square(df) at z standard deviations (p ~ 1e-6)
    return df * (1 - 2 / (9 * df) + z * math.sqrt(2 / (9 * df))) ** 3


def chi_square(seed):
    rng = random.Random(seed + 1)
    stats = []
    for kind in ('c8', 'pcg', 'cr'):
        for n in (3, 7, 10, 64, 100):
            k = 20000
            kw = {'key': [rng.randrange(1 << 32) for _ in range(8)]} if kind != 'pcg' else {'s1': rng.randrange(1 << 64), 's2': rng.randrange(1 << 64)}
            got = run(source_token(kind, **kw), ['c:%d:%d' % (n, k)])
            cs = [int(x) for x in got[0].split(',')]
            want = mirror(kind, **kw).call('c:%d:%d' % (n, k))
            check('chi counts %s n=%d' % (kind, n), got[0], want)
            e = k / n
            x2 = sum((c - e) ** 2 / e for c in cs)
            crit = chi_critical(n - 1)
            stats.append({'source': kind, 'n': n, 'draws': k, 'chi2': round(x2, 2), 'df': n - 1, 'critical_1e-6': round(crit, 2)})
            check('chi-square %s n=%d below critical' % (kind, n), sum(cs) == k and x2 < crit, True)
    return stats


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 2026
    go_vectors()
    differentials(seed)
    stats = chi_square(seed)
    verdict = {'checks': sum(COUNTS.values()), 'failures': FAILURES, 'seed': seed, 'chi_square': stats}
    print(json.dumps(verdict, indent=1))
    return 1 if FAILURES else 0


if __name__ == '__main__':
    sys.exit(main())
