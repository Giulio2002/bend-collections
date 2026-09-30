"""Shared shape of the generated invariants: a conjunction of Bool components.

The conjunction's suffixes are named defs (gr<i>: the components from i on),
so no statement repeats the rest of the chain: the projections g_<c> go one
and_right step at a time (gp<i>: the invariant gives the suffix from i on)
and good_intro builds it one and_intro per component. Written out inline the
same lemmas are quadratic in the number of components, and the checker keeps
every checked term, so they cost hundreds of MB.
"""


class Conj:
    def __init__(self, names, call, head):
        """names: the components in order; call(c, pre='', args=None) spells a
        call of c at the invariant's arguments; head: the parameter list every
        component takes."""
        self.names, self.call, self.head = names, call, head
        self.last = len(names) - 1

    def rest(self, i, pre="", args=None):
        """the conjunction of components i .. end"""
        if i == self.last:
            return self.call(self.names[i], pre, args)
        if i == 0:
            return self.call("goodF", pre, args)
        return self.call(f"gr{i}", pre, args)

    def body(self, i):
        if i == self.last:
            return self.call(self.names[i])
        return f"Bool.and({self.call(self.names[i])}, {self.rest(i + 1)})"

    @staticmethod
    def T(x):
        return "{" + x + " == True{} : Bool}"

    def suffixes(self):
        """gr<i> for the proper suffixes, last first, then goodF"""
        out = [f"def gr{i}({self.head}) -> Bool:\n  {self.body(i)}\n" for i in range(self.last - 1, 0, -1)]
        out.append(f"def goodF({self.head}) -> Bool:\n  {self.body(0)}\n")
        return out

    def projections(self, args):
        """gp<i> and g_<c>; args: the head's arguments as passed on"""
        T, call = self.T, self.call
        g = T(call("goodF"))
        out = []
        for i in range(1, len(self.names)):
            prev = "g" if i == 1 else call(f"gp{i - 1}", "", f"{args}, g")
            out.append(f"def gp{i}({self.head}, +g: {g}) -> {T(self.rest(i))}:\n"
                       f"  L.and_right({call(self.names[i - 1])}, {self.rest(i)}, {prev})\n")
        for i, c in enumerate(self.names):
            pr = "g" if i == 0 else call(f"gp{i}", "", f"{args}, g")
            body = f"L.and_left({call(c)}, {self.rest(i + 1)}, {pr})" if i < self.last else pr
            out.append(f"def g_{c}({self.head}, +g: {g}) -> {T(call(c))}:\n  {body}\n")
        return out

    def intro(self, i=0, hs=None):
        hs = hs or [f"h_{c}" for c in self.names]
        if i == self.last:
            return hs[i]
        return f"L.and_intro({self.call(self.names[i])}, {self.rest(i + 1)}, {hs[i]}, {self.intro(i + 1, hs)})"
