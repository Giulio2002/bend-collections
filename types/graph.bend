import Base

# Neutral datatypes shared by src/graph.bend and spec/graph.bend.

type Error is Data:
  VertexExists{}
  VertexNotFound{}
  SelfLoop{}
  EdgeNotFound{}

type Edge is Data:
  Edge{src: U32, dst: U32}

type Op is Data:
  AddVertex{v: U32}
  RemoveVertex{v: U32}
  AddEdge{u: U32, v: U32}
  RemoveEdge{u: U32, v: U32}
  HasVertex{v: U32}
  HasEdge{u: U32, v: U32}
  Neighbors{v: U32}
  Vertices{}
  Edges{}

type Obs is Data:
  OUnit{result: Result<&2, &2, Error, Unit>}
  OBool{value: Bool}
  OFlag{result: Result<&2, &2, Error, Bool>}
  ONeighbors{result: Result<&2, &2, Error, List<&2, U32>>}
  OVertices{vs: List<&2, U32>}
  OEdges{es: List<&2, Edge>}
