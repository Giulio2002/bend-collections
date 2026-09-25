import Base
import ./writes.bend as Writes
import ./graph.bend as Graph
import ./shape.bend as Shape
import ./edits.bend as Edits
import ./adapter.bend as Adapter
import ./history.bend as History
import ./array_adapter.bend as ArrayAdapter
import ./frames.bend as Frames
import ./example.bend as Example
import ./costs.bend as Costs

# Checked entry point. The semantic theorems apply to arbitrary identity and
# payload types through primitive adapter equations. array_adapter discharges
# all those equations for an actual owned-array representation; history proves
# arbitrary finite legal edit sequences, not a fixed test bound.
# See INTRUSIVE_LIST.md for theorem signatures and the adapter boundary.
