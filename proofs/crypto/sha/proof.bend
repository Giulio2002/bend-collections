import Base
import ../../../src/crypto/sha/sha256.bend as SHA
import ./correctness.bend as Correctness

law empty_vector:
  {SHA.sha256([]) == [3820012610, 2566659092, 2600203464, 2574235940,
    665731556, 1687917388, 2761267483, 2018687061] : List<&2, U32>}

law abc_vector:
  {SHA.sha256([97, 98, 99]) == [3128432319, 2399260650, 1094795486, 1571693091,
    2953011619, 2518121116, 3021012833, 4060091821] : List<&2, U32>}

def empty_vector():
  {==}

def abc_vector():
  {==}

law padding_boundary_vector:
  {SHA.sha256(SHA.ascii("abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq")) == [613247585, 3523623096, 3854575251, 205414457, 2738676825, 1694441831, 4142722516, 433784513] : List<&2, U32>}

def padding_boundary_vector():
  {==}

law multiblock_vector:
  {SHA.sha256(SHA.ascii("abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu")) == [3478853287, 2024768384, 57468318, 2063897143, 186948369, 3908074065, 2947302659, 2063526353] : List<&2, U32>}

def multiblock_vector():
  {==}
