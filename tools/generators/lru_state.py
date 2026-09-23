#!/usr/bin/env python3
"""Generate the LRU invariant (proofs/containers/lru/state.bend, after the marker
"# ---- the invariant (generated) ----").

The invariant is a conjunction of Bool components over the shadow's fields;
the generator writes each component, the conjunction goodF, one accessor
g_<c> per component, and good_intro, which builds goodF from the components.
"""
import pathlib

ROOT = pathlib.Path(__file__).resolve().parents[2]
STATE = ROOT / "proofs/containers/lru/state.bend"
MARK = "# ---- the invariant (generated) ----"

P = ("+cap: U32, +n: U32, +head: U32, +tail: U32, +free: U32, +fr: U32, +msz: U32, +mdp: U32, +mmk: U32, +mbt: U32, +pm: Bool, +k: Nat, +sd: Nat, "
     "+tabT: AR.Tree<U32>, +kl: List<&2, String>, +pk: Bool, +eT: AR.Tree<Maybe<&2, V>>, "
     "+lkT: AR.Tree<U32>, +sl: List<&2, Nat>, +fl: List<&2, Nat>")
A = "cap, n, head, tail, free, fr, msz, mdp, mmk, mbt, pm, k, sd, tabT, kl, pk, eT, lkT, sl, fl"
BS = "TB.buckets(AR.slots(U32, tabT), kl, SC.pow2(k))"
ML = "AR.slots(U32, mT)"
LL = "AR.slots(U32, lkT)"
EL = "AR.slots(Maybe<&2, V>, eT)"
FR = "UD.v(fr)"

COMPS = [
    ("ck", "Bool.and(Nat.is_lt(k, 30n), Nat.is_lt(0n, k))"),
    ("csdk", "Nat.is_lt(sd, k)"),
    ("cpt", "AR.perfect(U32, 1n+k, tabT)"),
    ("cpk", "pk"),
    ("cpe", "AR.perfect(Maybe<&2, V>, sd, eT)"),
    ("cpl", "AR.perfect(U32, 3n+sd, lkT)"),
    ("cpm", "pm"),
    ("cmask", "U32.is_eq(mmk, CY.msk(k))"),
    ("cbits", "Nat.is_eq(UD.v(mbt), k)"),
    ("csize", "Nat.is_eq(UD.v(msz), SC.pow2(sd))"),
    ("cdepth", "Nat.is_eq(UD.v(mdp), sd)"),
    ("cfresh", f"Nat.is_le({FR}, SC.pow2(sd))"),
    ("cwell", f"B.all_lt(B.PWell{{{BS}, sd}}, SC.pow2(k))"),
    ("cclus", f"B.cluster({BS}, SC.pow2(k), CY.msk(k))"),
    ("cuniq", f"B.all_lt(B.PUniq{{{BS}}}, SC.pow2(k))"),
    ("cn", f"Nat.is_eq(UD.v(n), IV.occn({BS}, SC.pow2(k)))"),
    ("cload", "Nat.is_le(Nat.double(UD.v(n)), SC.pow2(k))"),
    ("ccap", "Bool.not(U32.is_eq(cap, 0))"),
    ("cbsl", f"bsl({BS}, sl, {LL}, SC.pow2(k))"),
    ("chas", f"hasall(~V, {BS}, SC.pow2(k), {LL}, sl)"),
    ("csl", f"slok(~V, sl, {FR}, {EL})"),
    ("cnd", "NL.nodupn(sl)"),
    ("clen", "Nat.is_eq(SC.length(Nat, sl), UD.v(n))"),
    ("chead", "U32.is_eq(head, LK.fst_or(sl, 0))"),
    ("ctail", "U32.is_eq(tail, LK.last_or(sl, 0))"),
    ("cdll", f"seg({LL}, sl, 0, 0)"),
    ("ckeys", f"S.nodup(SP.keys_of(~V, es(~V, {LL}, kl, {EL}, sl)))"),
    ("cfree", "U32.is_eq(free, LK.fst_or(fl, 0))"),
    ("cfll", f"fll({LL}, fl)"),
    ("cfl", f"flok(~V, fl, {FR}, {EL})"),
    ("cfnd", "NL.nodupn(fl)"),
    ("cfcnt", f"Nat.is_eq(Nat.add(SC.length(Nat, sl), SC.length(Nat, fl)), {FR})"),
]
NAMES = [c for c, _ in COMPS]


def call(c, pre="", args=A):
    return f"{pre}{c}(~V, {args})"


def rest(i, pre="", args=A):
    if i == len(NAMES) - 1:
        return call(NAMES[i], pre, args)
    return f"Bool.and({call(NAMES[i], pre, args)}, {rest(i + 1, pre, args)})"


def T(x):
    return "{" + x + " == True{} : Bool}"


def intro(i, pre="", args=A, hs=None):
    hs = hs or [f"h_{c}" for c in NAMES]
    if i == len(NAMES) - 1:
        return hs[i]
    return f"L.and_intro({call(NAMES[i], pre, args)}, {rest(i + 1, pre, args)}, {hs[i]}, {intro(i + 1, pre, args, hs)})"


def block():
    out = [MARK, "# (tools/generators/lru_state.py)", ""]
    for c, body in COMPS:
        out.append(f"def {c}(~V: Data, {P}) -> Bool:\n  {body}\n")
    out.append(f"def goodF(~V: Data, {P}) -> Bool:\n  {rest(0)}\n")
    out.append('''def good(~V: Data, sh: Sh<V>) -> Bool:
  match sh:
    case LS{+cap, +n, +head, +tail, +free, +mT, +k, +sd, +tabT, +ksT, +eT, +lkT, +sl, +fl}:
      goodF(~V, cap, n, head, tail, free, W32.nth0(AR.slots(U32, mT), 0n), W32.nth0(AR.slots(U32, mT), 1n), W32.nth0(AR.slots(U32, mT), 2n), W32.nth0(AR.slots(U32, mT), 6n), W32.nth0(AR.slots(U32, mT), 7n), AR.perfect(U32, 5n, mT), k, sd, tabT, AR.slots(String, ksT), AR.perfect(String, sd, ksT), eT, lkT, sl, fl)
''')
    prs = ["g"]
    for i in range(len(NAMES) - 1):
        prs.append(f"L.and_right({call(NAMES[i])}, {rest(i + 1)}, {prs[i]})")
    for i, c in enumerate(NAMES):
        body = f"L.and_left({call(c)}, {rest(i + 1)}, {prs[i]})" if i < len(NAMES) - 1 else prs[i]
        out.append(f"def g_{c}(~V: Data, {P}, +g: {T(call('goodF'))}) -> {T(call(c))}:\n  {body}\n")
    hs = ", ".join(f"+h_{c}: {T(call(c))}" for c in NAMES)
    out.append("# the invariant from its components\n"
               f"def good_intro(~V: Data, {P}, {hs}) -> {T(call('goodF'))}:\n  {intro(0)}\n")
    return "\n".join(out)


def main():
    text = STATE.read_text()
    start = text.index(MARK)
    STATE.write_text(text[:start] + block())


if __name__ == "__main__":
    main()
