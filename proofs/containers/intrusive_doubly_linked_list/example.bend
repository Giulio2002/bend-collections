import Base
import ./graph.bend as G
import ./history.bend as H
import ./array_adapter.bend as A

# Non-vacuity witness: middle, head and tail removal, then identity reuse.
# Payload 42 is arbitrary; the general theorem quantifies over every P.
def initial() -> G.Graph<A.Node,A.Root,U32>:
  G.Graph{Nil{},Nil{},Nil{},42}

def edits() -> List<&2,H.Edit<A.Node>>:
  Con{H.Prepend{A.A{}},Con{H.Prepend{A.B{}},Con{H.Prepend{A.C{}},Con{H.RemoveAfter{Nil{},A.C{},A.B{},Con{A.A{},Nil{}}},Con{H.RemoveHead{A.C{},Con{A.A{},Nil{}}},Con{H.Prepend{A.B{}},Con{H.RemoveAfter{Nil{},A.B{},A.A{},Nil{}},Con{H.RemoveHead{A.B{},Nil{}},Nil{}}}}}}}}}

def initial_valid() -> G.valid(~A.Node,~A.Root,~U32,~A.eq,~A.req,initial(),A.Ready{},Nil{}):
  (Unit{},({==},Unit{}))

def history_legal() -> H.legal(~A.Node,~A.Root,~U32,~A.eq,~A.req,edits(),initial(),A.Ready{},Nil{}):
  ((Unit{},({==},{==})),(((({==},{==}),Unit{}),({==},{==})),(((({==},{==}),(({==},{==}),Unit{})),({==},{==})),({==},({==},(((({==},{==}),Unit{}),({==},{==})),({==},({==},Unit{}))))))))

# This proof uses the public-function refinement and invariant induction.
def correct() -> G.both({A.run(~U32,edits(),A.real(~U32,initial()),A.Ready{}) == A.real(~U32,H.run(~A.Node,~A.Root,~U32,~A.eq,~A.req,edits(),initial(),A.Ready{})) : A.Store<U32>},G.both(G.valid(~A.Node,~A.Root,~U32,~A.eq,~A.req,H.run(~A.Node,~A.Root,~U32,~A.eq,~A.req,edits(),initial(),A.Ready{}),A.Ready{},H.orders(~A.Node,edits(),Nil{})),{G.frame(~A.Node,~A.Root,~U32,H.run(~A.Node,~A.Root,~U32,~A.eq,~A.req,edits(),initial(),A.Ready{})) == 42 : U32})):
  A.histories_correct(~U32,edits(),initial(),A.Ready{},Nil{},history_legal(),initial_valid())
