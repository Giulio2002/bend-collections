import Base
import ../types/model.bend as T

# Abstract outcomes of requesting the caller's clock. Sample has already passed
# the signed-64-bit millisecond validation. The other constructors distinguish
# provider exceptions from rejected samples. A host conversion proof must map
# real provider outcomes to these cases; it is not assumed here.
type Event is Data:
  Sample{milliseconds: T.Int64}
  InvalidSample{reason: String}
  ProviderException{reason: String}

type Error is Data:
  Exhausted{}
  Invalid{reason: String}
  Thrown{reason: String}

type Reply is Data:
  Accepted{milliseconds: T.Int64, remaining: List<&2, Event>}
  Rejected{error: Error, remaining: List<&2, Event>}

# Each evaluation denotes exactly one request, including a failed request.
# Merely retaining a clock stream does not request or validate its next event.
def request(events: List<&2, Event>) -> Reply:
  match events:
    case Nil{}: Rejected{Exhausted{}, Nil{}}
    case Con{Sample{now}, tail}: Accepted{now, tail}
    case Con{InvalidSample{reason}, tail}: Rejected{Invalid{reason}, tail}
    case Con{ProviderException{reason}, tail}: Rejected{Thrown{reason}, tail}
