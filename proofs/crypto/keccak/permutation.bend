import Base
import ../../../src/crypto/keccak/types.bend as T
import ../../../src/crypto/keccak/permutation.bend as P
import ./spec_permutation.bend as S

law round_correct:
  for +s: T.State
  for +rc: T.Lane
  {P.round(s,rc) == S.round(s,rc) : T.State}

def round_correct(s,rc):
  match s rc:
    case T.S{T.W{a0,b0},T.W{a1,b1},T.W{a2,b2},T.W{a3,b3},T.W{a4,b4},T.W{a5,b5},T.W{a6,b6},T.W{a7,b7},T.W{a8,b8},T.W{a9,b9},T.W{a10,b10},T.W{a11,b11},T.W{a12,b12},T.W{a13,b13},T.W{a14,b14},T.W{a15,b15},T.W{a16,b16},T.W{a17,b17},T.W{a18,b18},T.W{a19,b19},T.W{a20,b20},T.W{a21,b21},T.W{a22,b22},T.W{a23,b23},T.W{a24,b24}} T.W{lo,hi}: {==}

law constants_correct:
  for +n: Nat
  {P.constant(n) == S.constant(n) : T.Lane}

def constants_correct(n):
  match n:
    case 0n: {==}
    case 1n: {==}
    case 2n: {==}
    case 3n: {==}
    case 4n: {==}
    case 5n: {==}
    case 6n: {==}
    case 7n: {==}
    case 8n: {==}
    case 9n: {==}
    case 10n: {==}
    case 11n: {==}
    case 12n: {==}
    case 13n: {==}
    case 14n: {==}
    case 15n: {==}
    case 16n: {==}
    case 17n: {==}
    case 18n: {==}
    case 19n: {==}
    case 20n: {==}
    case 21n: {==}
    case 22n: {==}
    case 23n: {==}
    case 24n+p: {==}


law pair_step:
  for +n: Nat
  for +i: Nat
  for +s: T.State
  {P.rounds(2n+n,i,s) == P.rounds(n,2n+i,P.round(P.round(s,P.constant(i)),P.constant(1n+i))) : T.State}

def pair_step(n,i,s):
  match s:
    case T.S{T.W{a0,b0},T.W{a1,b1},T.W{a2,b2},T.W{a3,b3},T.W{a4,b4},T.W{a5,b5},T.W{a6,b6},T.W{a7,b7},T.W{a8,b8},T.W{a9,b9},T.W{a10,b10},T.W{a11,b11},T.W{a12,b12},T.W{a13,b13},T.W{a14,b14},T.W{a15,b15},T.W{a16,b16},T.W{a17,b17},T.W{a18,b18},T.W{a19,b19},T.W{a20,b20},T.W{a21,b21},T.W{a22,b22},T.W{a23,b23},T.W{a24,b24}}: {==}

law single_step:
  for +i: Nat
  for +s: T.State
  {P.rounds(1n,i,s) == P.round(s,P.constant(i)) : T.State}

def single_step(i,s):
  {==}

law step_correct:
  for +i: Nat
  for +s: T.State
  {P.round(s,P.constant(i)) == S.round(s,S.constant(i)) : T.State}

def step_correct(i,s):
  Equal.trans(T.State,P.round(s,P.constant(i)),S.round(s,P.constant(i)),S.round(s,S.constant(i)),
    round_correct(s,P.constant(i)),
    Equal.cong(T.Lane,T.State,r => S.round(s,r),P.constant(i),S.constant(i),constants_correct(i)))

law two_correct:
  for +i: Nat
  for +s: T.State
  {P.round(P.round(s,P.constant(i)),P.constant(1n+i)) == S.round(S.round(s,S.constant(i)),S.constant(1n+i)) : T.State}

def two_correct(i,s):
  Equal.trans(T.State,
    P.round(P.round(s,P.constant(i)),P.constant(1n+i)),
    S.round(P.round(s,P.constant(i)),S.constant(1n+i)),
    S.round(S.round(s,S.constant(i)),S.constant(1n+i)),
    step_correct(1n+i,P.round(s,P.constant(i))),
    Equal.cong(T.State,T.State,t => S.round(t,S.constant(1n+i)),P.round(s,P.constant(i)),S.round(s,S.constant(i)),step_correct(i,s)))

law rounds_correct:
  for +n: Nat
  for +i: Nat
  for +s: T.State
  {P.rounds(n,i,s) == S.rounds(n,i,s) : T.State}

def rounds_correct(n,i,s):
  match n:
    case 0n: {==}
    case 1n:
      Equal.trans(T.State,P.rounds(1n,i,s),P.round(s,P.constant(i)),S.round(s,S.constant(i)),single_step(i,s),step_correct(i,s))
    case 2n+p:
      Equal.trans(T.State,P.rounds(2n+p,i,s),P.rounds(p,2n+i,P.round(P.round(s,P.constant(i)),P.constant(1n+i))),S.rounds(2n+p,i,s),pair_step(p,i,s),
        Equal.trans(T.State,
          P.rounds(p,2n+i,P.round(P.round(s,P.constant(i)),P.constant(1n+i))),
          S.rounds(p,2n+i,P.round(P.round(s,P.constant(i)),P.constant(1n+i))),
          S.rounds(p,2n+i,S.round(S.round(s,S.constant(i)),S.constant(1n+i))),
          rounds_correct(p,2n+i,P.round(P.round(s,P.constant(i)),P.constant(1n+i))),
          Equal.cong(T.State,T.State,t => S.rounds(p,2n+i,t),
            P.round(P.round(s,P.constant(i)),P.constant(1n+i)),S.round(S.round(s,S.constant(i)),S.constant(1n+i)),two_correct(i,s))))
