import Base
import ../src/cache.bend as C
import ../src/public.bend as Pub
import ../src/driver.bend as D
import ../spec/cache.bend as S
import ../spec/clock.bend as Clock
import ../spec/public_commands.bend as PC
import ../spec/traces.bend as Traces
import ../spec/equivalence.bend as E
import ../types/model.bend as T
import ./refinement.bend as F
import ./spec_lookup.bend as Lookup
import ./public_relation.bend as R
import ./public_trace.bend as PT
import ./rename_map.bend as RM
import ./rename_machine.bend as RN
import ./rename_spec.bend as RS
import ../src/codec.bend as Codec

# Refinement for any key type K with an injective codec enc and a specification
# key equality same that agrees with String equality of codes. The String
# theorem (public_trace.bend) is transported along the key renaming: the
# actual K machine renames to the String machine (rename_machine.bend) and the
# K specification renames to the String specification (rename_spec.bend).
# Replies, errors, unused events and request counts are then compared exactly
# at type K (renaming of replies is injective); final abstract states are
# compared canonically after renaming keys to their codes.

def commands(-K: Data, -V: Data, requests: List<&2, Pub.Request<K, V>>) -> List<&2, S.Command<K, V>>:
  match requests:
    case Nil{}: Nil{}
    case Con{request, tail}: Con{R.command(K, V, request), commands(K, V, tail)}

def command_rn(~K: Data, ~enc: K -> String, -V: Data, r: Pub.Request<K, V>) -> {R.command(String, V, RN.rn_request(~K, ~enc, V, r)) == RS.rn_command(~K, ~enc, V, R.command(K, V, r)) : S.Command<String, V>}:
  match r:
    case Pub.Add{k, v}: {==}
    case Pub.AddWithLifetime{k, v, ns}: {==}
    case Pub.Get{k}: {==}
    case Pub.GetAndRefresh{k, ns}: {==}
    case Pub.Peek{k}: {==}
    case Pub.Contains{k}: {==}
    case Pub.Remove{k}: {==}
    case Pub.RemoveOldest{}: {==}
    case Pub.GetOldest{}: {==}
    case Pub.Keys{}: {==}
    case Pub.Values{}: {==}
    case Pub.Purge{}: {==}
    case Pub.PurgeExpired{}: {==}
    case Pub.Len{}: {==}
    case Pub.SetLifetime{ns}: {==}
    case Pub.Metrics{}: {==}
    case Pub.ResetMetrics{}: {==}
    case Pub.Diagnostics{}: {==}

def commands_rn(~K: Data, ~enc: K -> String, -V: Data, requests: List<&2, Pub.Request<K, V>>) -> {PT.commands(V, RN.rn_requests(~K, ~enc, V, requests)) == RS.rn_commands(~K, ~enc, V, commands(K, V, requests)) : List<&2, S.Command<String, V>>}:
  match requests:
    case Nil{}: {==}
    case Con{+r, tail}:
      %Equal.sym(S.Command<String, V>, R.command(String, V, RN.rn_request(~K, ~enc, V, r)), RS.rn_command(~K, ~enc, V, R.command(K, V, r)), command_rn(~K, ~enc, V, r)) : {Con{_, PT.commands(V, RN.rn_requests(~K, ~enc, V, tail))} == RS.rn_commands(~K, ~enc, V, commands(K, V, Con{r, tail})) : List<&2, S.Command<String, V>>}
      Equal.cong(List<&2, S.Command<String, V>>, List<&2, S.Command<String, V>>, xs => Con{RS.rn_command(~K, ~enc, V, R.command(K, V, r)), xs}, PT.commands(V, RN.rn_requests(~K, ~enc, V, tail)), RS.rn_commands(~K, ~enc, V, commands(K, V, tail)), commands_rn(~K, ~enc, V, tail))

def reply_rn(~K: Data, ~enc: K -> String, -V: Data, a: Pub.Answer<K, V>) -> {R.reply(String, V, RN.rn_answer(~K, ~enc, V, a)) == RS.rn_reply(~K, ~enc, V, R.reply(K, V, a)) : PC.Reply<String, V>}:
  match a:
    case Pub.Empty{}: {==}
    case Pub.Boolean{b}: {==}
    case Pub.Value{v, f}: {==}
    case Pub.Oldest{k, v, f}: {==}
    case Pub.KeyList{ks}: {==}
    case Pub.ValueList{vs}: {==}
    case Pub.Length{n}: {==}
    case Pub.Counters{m}: {==}
    case Pub.Storage{l, r, c, m}: {==}

def reply_shape(-V: Data, a: PC.Reply<String, V>, b: PC.Reply<String, V>) -> Type:
  match a b:
    case PC.Unit{} PC.Unit{}: Unit
    case PC.Boolean{b1} PC.Boolean{b2}: Unit
    case PC.Value{v1, f1} PC.Value{v2, f2}: Unit
    case PC.Oldest{k1, v1, f1} PC.Oldest{k2, v2, f2}: Unit
    case PC.KeyList{ks1} PC.KeyList{ks2}: Unit
    case PC.ValueList{vs1} PC.ValueList{vs2}: Unit
    case PC.Length{n1} PC.Length{n2}: Unit
    case PC.Counters{m1} PC.Counters{m2}: Unit
    case PC.Storage{l1, r1, c1, m1} PC.Storage{l2, r2, c2, m2}: Unit
    case x y: Empty

def reply_shape_refl(-V: Data, a: PC.Reply<String, V>) -> reply_shape(V, a, a):
  match a:
    case PC.Unit{}: Unit{}
    case PC.Boolean{b}: Unit{}
    case PC.Value{v, f}: Unit{}
    case PC.Oldest{k, v, f}: Unit{}
    case PC.KeyList{ks}: Unit{}
    case PC.ValueList{vs}: Unit{}
    case PC.Length{n}: Unit{}
    case PC.Counters{m}: Unit{}
    case PC.Storage{l, r, c, m}: Unit{}

def reply_clash(-V: Data, a: PC.Reply<String, V>, b: PC.Reply<String, V>, e: {a == b : PC.Reply<String, V>}) -> reply_shape(V, a, b):
  %e : reply_shape(V, a, _)
  reply_shape_refl(V, a)

def list_shape(a: List<&2, String>, b: List<&2, String>) -> Type:
  match a b:
    case Nil{} Nil{}: Unit
    case Con{x, xs} Con{y, ys}: Unit
    case x y: Empty

def list_shape_refl(a: List<&2, String>) -> list_shape(a, a):
  match a:
    case Nil{}: Unit{}
    case Con{x, xs}: Unit{}

def list_clash(a: List<&2, String>, b: List<&2, String>, e: {a == b : List<&2, String>}) -> list_shape(a, b):
  %e : list_shape(a, _)
  list_shape_refl(a)

def list_head(xs: List<&2, String>, d: String) -> String:
  match xs:
    case Nil{}: d
    case Con{x, rest}: x

def list_tail(xs: List<&2, String>) -> List<&2, String>:
  match xs:
    case Nil{}: Nil{}
    case Con{x, rest}: rest

def cons_equal(-K: Data, +x: K, +y: K, +xs: List<&2, K>, +ys: List<&2, K>, ex: {x == y : K}, es: {xs == ys : List<&2, K>}) -> {Con{x, xs} == Con{y, ys} : List<&2, K>}:
  %ex : {Con{x, xs} == Con{_, ys} : List<&2, K>}
  %es : {Con{x, xs} == Con{x, _} : List<&2, K>}
  {==}

def keys_injective(~K: Data, ~enc: K -> String, ~inj: @a: K -> @b: K -> @e: {enc(a) == enc(b) : String} -> {a == b : K}, xs: List<&2, K>, ys: List<&2, K>, +e: {RN.rn_keys(~K, ~enc, xs) == RN.rn_keys(~K, ~enc, ys) : List<&2, String>}) -> {xs == ys : List<&2, K>}:
  match xs ys:
    case Nil{} Nil{}: {==}
    case Nil{} Con{y, rest}: Empty.absurd({Nil{} == Con{y, rest} : List<&2, K>}, list_clash(Nil{}, RN.rn_keys(~K, ~enc, Con{y, rest}), e))
    case Con{x, rest} Nil{}: Empty.absurd({Con{x, rest} == Nil{} : List<&2, K>}, list_clash(RN.rn_keys(~K, ~enc, Con{x, rest}), Nil{}, e))
    case Con{+x, +xs2} Con{+y, +ys2}: cons_equal(K, x, y, xs2, ys2, inj(x, y, Equal.cong(List<&2, String>, String, l => list_head(l, enc(x)), Con{enc(x), RN.rn_keys(~K, ~enc, xs2)}, Con{enc(y), RN.rn_keys(~K, ~enc, ys2)}, e)), keys_injective(~K, ~enc, ~inj, xs2, ys2, Equal.cong(List<&2, String>, List<&2, String>, l => list_tail(l), Con{enc(x), RN.rn_keys(~K, ~enc, xs2)}, Con{enc(y), RN.rn_keys(~K, ~enc, ys2)}, e)))

def oldest_key(-V: Data, r: PC.Reply<String, V>, d: String) -> String:
  match r:
    case PC.Oldest{k, v, f}: k
    case x: d

def oldest_value(-V: Data, r: PC.Reply<String, V>, d: V) -> V:
  match r:
    case PC.Oldest{k, v, f}: v
    case x: d

def oldest_found(-V: Data, r: PC.Reply<String, V>, d: Bool) -> Bool:
  match r:
    case PC.Oldest{k, v, f}: f
    case x: d

def key_list(-V: Data, r: PC.Reply<String, V>, d: List<&2, String>) -> List<&2, String>:
  match r:
    case PC.KeyList{ks}: ks
    case x: d

# Key-free reply constructors carry over unchanged between key types.
def retype(-K: Data, -V: Data, r: PC.Reply<String, V>, d: PC.Reply<K, V>) -> PC.Reply<K, V>:
  match r:
    case PC.Unit{}: PC.Unit{}
    case PC.Boolean{b}: PC.Boolean{b}
    case PC.Value{v, f}: PC.Value{v, f}
    case PC.Oldest{k, v, f}: d
    case PC.KeyList{ks}: d
    case PC.ValueList{vs}: PC.ValueList{vs}
    case PC.Length{n}: PC.Length{n}
    case PC.Counters{m}: PC.Counters{m}
    case PC.Storage{l, r2, c, m}: PC.Storage{l, r2, c, m}

def oldest_equal(-K: Data, -V: Data, +k1: K, +k2: K, +v1: V, +v2: V, +f1: Bool, +f2: Bool, ek: {k1 == k2 : K}, ev: {v1 == v2 : V}, ef: {f1 == f2 : Bool}) -> {PC.Oldest{k1, v1, f1} == PC.Oldest{k2, v2, f2} : PC.Reply<K, V>}:
  %ek : {PC.Oldest{k1, v1, f1} == PC.Oldest{_, v2, f2} : PC.Reply<K, V>}
  %ev : {PC.Oldest{k1, v1, f1} == PC.Oldest{k1, _, f2} : PC.Reply<K, V>}
  %ef : {PC.Oldest{k1, v1, f1} == PC.Oldest{k1, v1, _} : PC.Reply<K, V>}
  {==}

def reply_injective(~K: Data, ~enc: K -> String, ~inj: @a: K -> @b: K -> @e: {enc(a) == enc(b) : String} -> {a == b : K}, -V: Data, x: PC.Reply<K, V>, y: PC.Reply<K, V>, +e: {RS.rn_reply(~K, ~enc, V, x) == RS.rn_reply(~K, ~enc, V, y) : PC.Reply<String, V>}) -> {x == y : PC.Reply<K, V>}:
  match x:
    case PC.Unit{}:
      match y:
        case PC.Unit{}: {==}
        case PC.Boolean{b2}: Empty.absurd({PC.Unit{} == PC.Boolean{b2} : PC.Reply<K, V>}, reply_clash(V, RS.rn_reply(~K, ~enc, V, PC.Unit{}), RS.rn_reply(~K, ~enc, V, PC.Boolean{b2}), e))
        case PC.Value{v2, f2}: Empty.absurd({PC.Unit{} == PC.Value{v2, f2} : PC.Reply<K, V>}, reply_clash(V, RS.rn_reply(~K, ~enc, V, PC.Unit{}), RS.rn_reply(~K, ~enc, V, PC.Value{v2, f2}), e))
        case PC.Oldest{k2, v2, f2}: Empty.absurd({PC.Unit{} == PC.Oldest{k2, v2, f2} : PC.Reply<K, V>}, reply_clash(V, RS.rn_reply(~K, ~enc, V, PC.Unit{}), RS.rn_reply(~K, ~enc, V, PC.Oldest{k2, v2, f2}), e))
        case PC.KeyList{ks2}: Empty.absurd({PC.Unit{} == PC.KeyList{ks2} : PC.Reply<K, V>}, reply_clash(V, RS.rn_reply(~K, ~enc, V, PC.Unit{}), RS.rn_reply(~K, ~enc, V, PC.KeyList{ks2}), e))
        case PC.ValueList{vs2}: Empty.absurd({PC.Unit{} == PC.ValueList{vs2} : PC.Reply<K, V>}, reply_clash(V, RS.rn_reply(~K, ~enc, V, PC.Unit{}), RS.rn_reply(~K, ~enc, V, PC.ValueList{vs2}), e))
        case PC.Length{n2}: Empty.absurd({PC.Unit{} == PC.Length{n2} : PC.Reply<K, V>}, reply_clash(V, RS.rn_reply(~K, ~enc, V, PC.Unit{}), RS.rn_reply(~K, ~enc, V, PC.Length{n2}), e))
        case PC.Counters{m2}: Empty.absurd({PC.Unit{} == PC.Counters{m2} : PC.Reply<K, V>}, reply_clash(V, RS.rn_reply(~K, ~enc, V, PC.Unit{}), RS.rn_reply(~K, ~enc, V, PC.Counters{m2}), e))
        case PC.Storage{l2, r2, c2, m2}: Empty.absurd({PC.Unit{} == PC.Storage{l2, r2, c2, m2} : PC.Reply<K, V>}, reply_clash(V, RS.rn_reply(~K, ~enc, V, PC.Unit{}), RS.rn_reply(~K, ~enc, V, PC.Storage{l2, r2, c2, m2}), e))
    case PC.Boolean{+b1}:
      match y:
        case PC.Unit{}: Empty.absurd({PC.Boolean{b1} == PC.Unit{} : PC.Reply<K, V>}, reply_clash(V, RS.rn_reply(~K, ~enc, V, PC.Boolean{b1}), RS.rn_reply(~K, ~enc, V, PC.Unit{}), e))
        case PC.Boolean{+b2}: Equal.cong(PC.Reply<String, V>, PC.Reply<K, V>, r => retype(K, V, r, PC.Boolean{b1}), RS.rn_reply(~K, ~enc, V, PC.Boolean{b1}), RS.rn_reply(~K, ~enc, V, PC.Boolean{b2}), e)
        case PC.Value{v2, f2}: Empty.absurd({PC.Boolean{b1} == PC.Value{v2, f2} : PC.Reply<K, V>}, reply_clash(V, RS.rn_reply(~K, ~enc, V, PC.Boolean{b1}), RS.rn_reply(~K, ~enc, V, PC.Value{v2, f2}), e))
        case PC.Oldest{k2, v2, f2}: Empty.absurd({PC.Boolean{b1} == PC.Oldest{k2, v2, f2} : PC.Reply<K, V>}, reply_clash(V, RS.rn_reply(~K, ~enc, V, PC.Boolean{b1}), RS.rn_reply(~K, ~enc, V, PC.Oldest{k2, v2, f2}), e))
        case PC.KeyList{ks2}: Empty.absurd({PC.Boolean{b1} == PC.KeyList{ks2} : PC.Reply<K, V>}, reply_clash(V, RS.rn_reply(~K, ~enc, V, PC.Boolean{b1}), RS.rn_reply(~K, ~enc, V, PC.KeyList{ks2}), e))
        case PC.ValueList{vs2}: Empty.absurd({PC.Boolean{b1} == PC.ValueList{vs2} : PC.Reply<K, V>}, reply_clash(V, RS.rn_reply(~K, ~enc, V, PC.Boolean{b1}), RS.rn_reply(~K, ~enc, V, PC.ValueList{vs2}), e))
        case PC.Length{n2}: Empty.absurd({PC.Boolean{b1} == PC.Length{n2} : PC.Reply<K, V>}, reply_clash(V, RS.rn_reply(~K, ~enc, V, PC.Boolean{b1}), RS.rn_reply(~K, ~enc, V, PC.Length{n2}), e))
        case PC.Counters{m2}: Empty.absurd({PC.Boolean{b1} == PC.Counters{m2} : PC.Reply<K, V>}, reply_clash(V, RS.rn_reply(~K, ~enc, V, PC.Boolean{b1}), RS.rn_reply(~K, ~enc, V, PC.Counters{m2}), e))
        case PC.Storage{l2, r2, c2, m2}: Empty.absurd({PC.Boolean{b1} == PC.Storage{l2, r2, c2, m2} : PC.Reply<K, V>}, reply_clash(V, RS.rn_reply(~K, ~enc, V, PC.Boolean{b1}), RS.rn_reply(~K, ~enc, V, PC.Storage{l2, r2, c2, m2}), e))
    case PC.Value{+v1, f1}:
      match y:
        case PC.Unit{}: Empty.absurd({PC.Value{v1, f1} == PC.Unit{} : PC.Reply<K, V>}, reply_clash(V, RS.rn_reply(~K, ~enc, V, PC.Value{v1, f1}), RS.rn_reply(~K, ~enc, V, PC.Unit{}), e))
        case PC.Boolean{b2}: Empty.absurd({PC.Value{v1, f1} == PC.Boolean{b2} : PC.Reply<K, V>}, reply_clash(V, RS.rn_reply(~K, ~enc, V, PC.Value{v1, f1}), RS.rn_reply(~K, ~enc, V, PC.Boolean{b2}), e))
        case PC.Value{+v2, f2}: Equal.cong(PC.Reply<String, V>, PC.Reply<K, V>, r => retype(K, V, r, PC.Value{v1, f1}), RS.rn_reply(~K, ~enc, V, PC.Value{v1, f1}), RS.rn_reply(~K, ~enc, V, PC.Value{v2, f2}), e)
        case PC.Oldest{k2, v2, f2}: Empty.absurd({PC.Value{v1, f1} == PC.Oldest{k2, v2, f2} : PC.Reply<K, V>}, reply_clash(V, RS.rn_reply(~K, ~enc, V, PC.Value{v1, f1}), RS.rn_reply(~K, ~enc, V, PC.Oldest{k2, v2, f2}), e))
        case PC.KeyList{ks2}: Empty.absurd({PC.Value{v1, f1} == PC.KeyList{ks2} : PC.Reply<K, V>}, reply_clash(V, RS.rn_reply(~K, ~enc, V, PC.Value{v1, f1}), RS.rn_reply(~K, ~enc, V, PC.KeyList{ks2}), e))
        case PC.ValueList{vs2}: Empty.absurd({PC.Value{v1, f1} == PC.ValueList{vs2} : PC.Reply<K, V>}, reply_clash(V, RS.rn_reply(~K, ~enc, V, PC.Value{v1, f1}), RS.rn_reply(~K, ~enc, V, PC.ValueList{vs2}), e))
        case PC.Length{n2}: Empty.absurd({PC.Value{v1, f1} == PC.Length{n2} : PC.Reply<K, V>}, reply_clash(V, RS.rn_reply(~K, ~enc, V, PC.Value{v1, f1}), RS.rn_reply(~K, ~enc, V, PC.Length{n2}), e))
        case PC.Counters{m2}: Empty.absurd({PC.Value{v1, f1} == PC.Counters{m2} : PC.Reply<K, V>}, reply_clash(V, RS.rn_reply(~K, ~enc, V, PC.Value{v1, f1}), RS.rn_reply(~K, ~enc, V, PC.Counters{m2}), e))
        case PC.Storage{l2, r2, c2, m2}: Empty.absurd({PC.Value{v1, f1} == PC.Storage{l2, r2, c2, m2} : PC.Reply<K, V>}, reply_clash(V, RS.rn_reply(~K, ~enc, V, PC.Value{v1, f1}), RS.rn_reply(~K, ~enc, V, PC.Storage{l2, r2, c2, m2}), e))
    case PC.Oldest{+k1, v1, f1}:
      match y:
        case PC.Unit{}: Empty.absurd({PC.Oldest{k1, v1, f1} == PC.Unit{} : PC.Reply<K, V>}, reply_clash(V, RS.rn_reply(~K, ~enc, V, PC.Oldest{k1, v1, f1}), RS.rn_reply(~K, ~enc, V, PC.Unit{}), e))
        case PC.Boolean{b2}: Empty.absurd({PC.Oldest{k1, v1, f1} == PC.Boolean{b2} : PC.Reply<K, V>}, reply_clash(V, RS.rn_reply(~K, ~enc, V, PC.Oldest{k1, v1, f1}), RS.rn_reply(~K, ~enc, V, PC.Boolean{b2}), e))
        case PC.Value{v2, f2}: Empty.absurd({PC.Oldest{k1, v1, f1} == PC.Value{v2, f2} : PC.Reply<K, V>}, reply_clash(V, RS.rn_reply(~K, ~enc, V, PC.Oldest{k1, v1, f1}), RS.rn_reply(~K, ~enc, V, PC.Value{v2, f2}), e))
        case PC.Oldest{+k2, v2, f2}: oldest_equal(K, V, k1, k2, v1, v2, f1, f2, inj(k1, k2, Equal.cong(PC.Reply<String, V>, String, r => oldest_key(V, r, enc(k1)), PC.Oldest{enc(k1), v1, f1}, PC.Oldest{enc(k2), v2, f2}, e)), Equal.cong(PC.Reply<String, V>, V, r => oldest_value(V, r, v1), PC.Oldest{enc(k1), v1, f1}, PC.Oldest{enc(k2), v2, f2}, e), Equal.cong(PC.Reply<String, V>, Bool, r => oldest_found(V, r, f1), PC.Oldest{enc(k1), v1, f1}, PC.Oldest{enc(k2), v2, f2}, e))
        case PC.KeyList{ks2}: Empty.absurd({PC.Oldest{k1, v1, f1} == PC.KeyList{ks2} : PC.Reply<K, V>}, reply_clash(V, RS.rn_reply(~K, ~enc, V, PC.Oldest{k1, v1, f1}), RS.rn_reply(~K, ~enc, V, PC.KeyList{ks2}), e))
        case PC.ValueList{vs2}: Empty.absurd({PC.Oldest{k1, v1, f1} == PC.ValueList{vs2} : PC.Reply<K, V>}, reply_clash(V, RS.rn_reply(~K, ~enc, V, PC.Oldest{k1, v1, f1}), RS.rn_reply(~K, ~enc, V, PC.ValueList{vs2}), e))
        case PC.Length{n2}: Empty.absurd({PC.Oldest{k1, v1, f1} == PC.Length{n2} : PC.Reply<K, V>}, reply_clash(V, RS.rn_reply(~K, ~enc, V, PC.Oldest{k1, v1, f1}), RS.rn_reply(~K, ~enc, V, PC.Length{n2}), e))
        case PC.Counters{m2}: Empty.absurd({PC.Oldest{k1, v1, f1} == PC.Counters{m2} : PC.Reply<K, V>}, reply_clash(V, RS.rn_reply(~K, ~enc, V, PC.Oldest{k1, v1, f1}), RS.rn_reply(~K, ~enc, V, PC.Counters{m2}), e))
        case PC.Storage{l2, r2, c2, m2}: Empty.absurd({PC.Oldest{k1, v1, f1} == PC.Storage{l2, r2, c2, m2} : PC.Reply<K, V>}, reply_clash(V, RS.rn_reply(~K, ~enc, V, PC.Oldest{k1, v1, f1}), RS.rn_reply(~K, ~enc, V, PC.Storage{l2, r2, c2, m2}), e))
    case PC.KeyList{+ks1}:
      match y:
        case PC.Unit{}: Empty.absurd({PC.KeyList{ks1} == PC.Unit{} : PC.Reply<K, V>}, reply_clash(V, RS.rn_reply(~K, ~enc, V, PC.KeyList{ks1}), RS.rn_reply(~K, ~enc, V, PC.Unit{}), e))
        case PC.Boolean{b2}: Empty.absurd({PC.KeyList{ks1} == PC.Boolean{b2} : PC.Reply<K, V>}, reply_clash(V, RS.rn_reply(~K, ~enc, V, PC.KeyList{ks1}), RS.rn_reply(~K, ~enc, V, PC.Boolean{b2}), e))
        case PC.Value{v2, f2}: Empty.absurd({PC.KeyList{ks1} == PC.Value{v2, f2} : PC.Reply<K, V>}, reply_clash(V, RS.rn_reply(~K, ~enc, V, PC.KeyList{ks1}), RS.rn_reply(~K, ~enc, V, PC.Value{v2, f2}), e))
        case PC.Oldest{k2, v2, f2}: Empty.absurd({PC.KeyList{ks1} == PC.Oldest{k2, v2, f2} : PC.Reply<K, V>}, reply_clash(V, RS.rn_reply(~K, ~enc, V, PC.KeyList{ks1}), RS.rn_reply(~K, ~enc, V, PC.Oldest{k2, v2, f2}), e))
        case PC.KeyList{+ks2}: Equal.cong(List<&2, K>, PC.Reply<K, V>, l => PC.KeyList{l}, ks1, ks2, keys_injective(~K, ~enc, ~inj, ks1, ks2, Equal.cong(PC.Reply<String, V>, List<&2, String>, r => key_list(V, r, RN.rn_keys(~K, ~enc, ks1)), PC.KeyList{RN.rn_keys(~K, ~enc, ks1)}, PC.KeyList{RN.rn_keys(~K, ~enc, ks2)}, e)))
        case PC.ValueList{vs2}: Empty.absurd({PC.KeyList{ks1} == PC.ValueList{vs2} : PC.Reply<K, V>}, reply_clash(V, RS.rn_reply(~K, ~enc, V, PC.KeyList{ks1}), RS.rn_reply(~K, ~enc, V, PC.ValueList{vs2}), e))
        case PC.Length{n2}: Empty.absurd({PC.KeyList{ks1} == PC.Length{n2} : PC.Reply<K, V>}, reply_clash(V, RS.rn_reply(~K, ~enc, V, PC.KeyList{ks1}), RS.rn_reply(~K, ~enc, V, PC.Length{n2}), e))
        case PC.Counters{m2}: Empty.absurd({PC.KeyList{ks1} == PC.Counters{m2} : PC.Reply<K, V>}, reply_clash(V, RS.rn_reply(~K, ~enc, V, PC.KeyList{ks1}), RS.rn_reply(~K, ~enc, V, PC.Counters{m2}), e))
        case PC.Storage{l2, r2, c2, m2}: Empty.absurd({PC.KeyList{ks1} == PC.Storage{l2, r2, c2, m2} : PC.Reply<K, V>}, reply_clash(V, RS.rn_reply(~K, ~enc, V, PC.KeyList{ks1}), RS.rn_reply(~K, ~enc, V, PC.Storage{l2, r2, c2, m2}), e))
    case PC.ValueList{+vs1}:
      match y:
        case PC.Unit{}: Empty.absurd({PC.ValueList{vs1} == PC.Unit{} : PC.Reply<K, V>}, reply_clash(V, RS.rn_reply(~K, ~enc, V, PC.ValueList{vs1}), RS.rn_reply(~K, ~enc, V, PC.Unit{}), e))
        case PC.Boolean{b2}: Empty.absurd({PC.ValueList{vs1} == PC.Boolean{b2} : PC.Reply<K, V>}, reply_clash(V, RS.rn_reply(~K, ~enc, V, PC.ValueList{vs1}), RS.rn_reply(~K, ~enc, V, PC.Boolean{b2}), e))
        case PC.Value{v2, f2}: Empty.absurd({PC.ValueList{vs1} == PC.Value{v2, f2} : PC.Reply<K, V>}, reply_clash(V, RS.rn_reply(~K, ~enc, V, PC.ValueList{vs1}), RS.rn_reply(~K, ~enc, V, PC.Value{v2, f2}), e))
        case PC.Oldest{k2, v2, f2}: Empty.absurd({PC.ValueList{vs1} == PC.Oldest{k2, v2, f2} : PC.Reply<K, V>}, reply_clash(V, RS.rn_reply(~K, ~enc, V, PC.ValueList{vs1}), RS.rn_reply(~K, ~enc, V, PC.Oldest{k2, v2, f2}), e))
        case PC.KeyList{ks2}: Empty.absurd({PC.ValueList{vs1} == PC.KeyList{ks2} : PC.Reply<K, V>}, reply_clash(V, RS.rn_reply(~K, ~enc, V, PC.ValueList{vs1}), RS.rn_reply(~K, ~enc, V, PC.KeyList{ks2}), e))
        case PC.ValueList{+vs2}: Equal.cong(PC.Reply<String, V>, PC.Reply<K, V>, r => retype(K, V, r, PC.ValueList{vs1}), RS.rn_reply(~K, ~enc, V, PC.ValueList{vs1}), RS.rn_reply(~K, ~enc, V, PC.ValueList{vs2}), e)
        case PC.Length{n2}: Empty.absurd({PC.ValueList{vs1} == PC.Length{n2} : PC.Reply<K, V>}, reply_clash(V, RS.rn_reply(~K, ~enc, V, PC.ValueList{vs1}), RS.rn_reply(~K, ~enc, V, PC.Length{n2}), e))
        case PC.Counters{m2}: Empty.absurd({PC.ValueList{vs1} == PC.Counters{m2} : PC.Reply<K, V>}, reply_clash(V, RS.rn_reply(~K, ~enc, V, PC.ValueList{vs1}), RS.rn_reply(~K, ~enc, V, PC.Counters{m2}), e))
        case PC.Storage{l2, r2, c2, m2}: Empty.absurd({PC.ValueList{vs1} == PC.Storage{l2, r2, c2, m2} : PC.Reply<K, V>}, reply_clash(V, RS.rn_reply(~K, ~enc, V, PC.ValueList{vs1}), RS.rn_reply(~K, ~enc, V, PC.Storage{l2, r2, c2, m2}), e))
    case PC.Length{+n1}:
      match y:
        case PC.Unit{}: Empty.absurd({PC.Length{n1} == PC.Unit{} : PC.Reply<K, V>}, reply_clash(V, RS.rn_reply(~K, ~enc, V, PC.Length{n1}), RS.rn_reply(~K, ~enc, V, PC.Unit{}), e))
        case PC.Boolean{b2}: Empty.absurd({PC.Length{n1} == PC.Boolean{b2} : PC.Reply<K, V>}, reply_clash(V, RS.rn_reply(~K, ~enc, V, PC.Length{n1}), RS.rn_reply(~K, ~enc, V, PC.Boolean{b2}), e))
        case PC.Value{v2, f2}: Empty.absurd({PC.Length{n1} == PC.Value{v2, f2} : PC.Reply<K, V>}, reply_clash(V, RS.rn_reply(~K, ~enc, V, PC.Length{n1}), RS.rn_reply(~K, ~enc, V, PC.Value{v2, f2}), e))
        case PC.Oldest{k2, v2, f2}: Empty.absurd({PC.Length{n1} == PC.Oldest{k2, v2, f2} : PC.Reply<K, V>}, reply_clash(V, RS.rn_reply(~K, ~enc, V, PC.Length{n1}), RS.rn_reply(~K, ~enc, V, PC.Oldest{k2, v2, f2}), e))
        case PC.KeyList{ks2}: Empty.absurd({PC.Length{n1} == PC.KeyList{ks2} : PC.Reply<K, V>}, reply_clash(V, RS.rn_reply(~K, ~enc, V, PC.Length{n1}), RS.rn_reply(~K, ~enc, V, PC.KeyList{ks2}), e))
        case PC.ValueList{vs2}: Empty.absurd({PC.Length{n1} == PC.ValueList{vs2} : PC.Reply<K, V>}, reply_clash(V, RS.rn_reply(~K, ~enc, V, PC.Length{n1}), RS.rn_reply(~K, ~enc, V, PC.ValueList{vs2}), e))
        case PC.Length{+n2}: Equal.cong(PC.Reply<String, V>, PC.Reply<K, V>, r => retype(K, V, r, PC.Length{n1}), RS.rn_reply(~K, ~enc, V, PC.Length{n1}), RS.rn_reply(~K, ~enc, V, PC.Length{n2}), e)
        case PC.Counters{m2}: Empty.absurd({PC.Length{n1} == PC.Counters{m2} : PC.Reply<K, V>}, reply_clash(V, RS.rn_reply(~K, ~enc, V, PC.Length{n1}), RS.rn_reply(~K, ~enc, V, PC.Counters{m2}), e))
        case PC.Storage{l2, r2, c2, m2}: Empty.absurd({PC.Length{n1} == PC.Storage{l2, r2, c2, m2} : PC.Reply<K, V>}, reply_clash(V, RS.rn_reply(~K, ~enc, V, PC.Length{n1}), RS.rn_reply(~K, ~enc, V, PC.Storage{l2, r2, c2, m2}), e))
    case PC.Counters{+m1}:
      match y:
        case PC.Unit{}: Empty.absurd({PC.Counters{m1} == PC.Unit{} : PC.Reply<K, V>}, reply_clash(V, RS.rn_reply(~K, ~enc, V, PC.Counters{m1}), RS.rn_reply(~K, ~enc, V, PC.Unit{}), e))
        case PC.Boolean{b2}: Empty.absurd({PC.Counters{m1} == PC.Boolean{b2} : PC.Reply<K, V>}, reply_clash(V, RS.rn_reply(~K, ~enc, V, PC.Counters{m1}), RS.rn_reply(~K, ~enc, V, PC.Boolean{b2}), e))
        case PC.Value{v2, f2}: Empty.absurd({PC.Counters{m1} == PC.Value{v2, f2} : PC.Reply<K, V>}, reply_clash(V, RS.rn_reply(~K, ~enc, V, PC.Counters{m1}), RS.rn_reply(~K, ~enc, V, PC.Value{v2, f2}), e))
        case PC.Oldest{k2, v2, f2}: Empty.absurd({PC.Counters{m1} == PC.Oldest{k2, v2, f2} : PC.Reply<K, V>}, reply_clash(V, RS.rn_reply(~K, ~enc, V, PC.Counters{m1}), RS.rn_reply(~K, ~enc, V, PC.Oldest{k2, v2, f2}), e))
        case PC.KeyList{ks2}: Empty.absurd({PC.Counters{m1} == PC.KeyList{ks2} : PC.Reply<K, V>}, reply_clash(V, RS.rn_reply(~K, ~enc, V, PC.Counters{m1}), RS.rn_reply(~K, ~enc, V, PC.KeyList{ks2}), e))
        case PC.ValueList{vs2}: Empty.absurd({PC.Counters{m1} == PC.ValueList{vs2} : PC.Reply<K, V>}, reply_clash(V, RS.rn_reply(~K, ~enc, V, PC.Counters{m1}), RS.rn_reply(~K, ~enc, V, PC.ValueList{vs2}), e))
        case PC.Length{n2}: Empty.absurd({PC.Counters{m1} == PC.Length{n2} : PC.Reply<K, V>}, reply_clash(V, RS.rn_reply(~K, ~enc, V, PC.Counters{m1}), RS.rn_reply(~K, ~enc, V, PC.Length{n2}), e))
        case PC.Counters{+m2}: Equal.cong(PC.Reply<String, V>, PC.Reply<K, V>, r => retype(K, V, r, PC.Counters{m1}), RS.rn_reply(~K, ~enc, V, PC.Counters{m1}), RS.rn_reply(~K, ~enc, V, PC.Counters{m2}), e)
        case PC.Storage{l2, r2, c2, m2}: Empty.absurd({PC.Counters{m1} == PC.Storage{l2, r2, c2, m2} : PC.Reply<K, V>}, reply_clash(V, RS.rn_reply(~K, ~enc, V, PC.Counters{m1}), RS.rn_reply(~K, ~enc, V, PC.Storage{l2, r2, c2, m2}), e))
    case PC.Storage{+l1, r1, c1, m1}:
      match y:
        case PC.Unit{}: Empty.absurd({PC.Storage{l1, r1, c1, m1} == PC.Unit{} : PC.Reply<K, V>}, reply_clash(V, RS.rn_reply(~K, ~enc, V, PC.Storage{l1, r1, c1, m1}), RS.rn_reply(~K, ~enc, V, PC.Unit{}), e))
        case PC.Boolean{b2}: Empty.absurd({PC.Storage{l1, r1, c1, m1} == PC.Boolean{b2} : PC.Reply<K, V>}, reply_clash(V, RS.rn_reply(~K, ~enc, V, PC.Storage{l1, r1, c1, m1}), RS.rn_reply(~K, ~enc, V, PC.Boolean{b2}), e))
        case PC.Value{v2, f2}: Empty.absurd({PC.Storage{l1, r1, c1, m1} == PC.Value{v2, f2} : PC.Reply<K, V>}, reply_clash(V, RS.rn_reply(~K, ~enc, V, PC.Storage{l1, r1, c1, m1}), RS.rn_reply(~K, ~enc, V, PC.Value{v2, f2}), e))
        case PC.Oldest{k2, v2, f2}: Empty.absurd({PC.Storage{l1, r1, c1, m1} == PC.Oldest{k2, v2, f2} : PC.Reply<K, V>}, reply_clash(V, RS.rn_reply(~K, ~enc, V, PC.Storage{l1, r1, c1, m1}), RS.rn_reply(~K, ~enc, V, PC.Oldest{k2, v2, f2}), e))
        case PC.KeyList{ks2}: Empty.absurd({PC.Storage{l1, r1, c1, m1} == PC.KeyList{ks2} : PC.Reply<K, V>}, reply_clash(V, RS.rn_reply(~K, ~enc, V, PC.Storage{l1, r1, c1, m1}), RS.rn_reply(~K, ~enc, V, PC.KeyList{ks2}), e))
        case PC.ValueList{vs2}: Empty.absurd({PC.Storage{l1, r1, c1, m1} == PC.ValueList{vs2} : PC.Reply<K, V>}, reply_clash(V, RS.rn_reply(~K, ~enc, V, PC.Storage{l1, r1, c1, m1}), RS.rn_reply(~K, ~enc, V, PC.ValueList{vs2}), e))
        case PC.Length{n2}: Empty.absurd({PC.Storage{l1, r1, c1, m1} == PC.Length{n2} : PC.Reply<K, V>}, reply_clash(V, RS.rn_reply(~K, ~enc, V, PC.Storage{l1, r1, c1, m1}), RS.rn_reply(~K, ~enc, V, PC.Length{n2}), e))
        case PC.Counters{m2}: Empty.absurd({PC.Storage{l1, r1, c1, m1} == PC.Counters{m2} : PC.Reply<K, V>}, reply_clash(V, RS.rn_reply(~K, ~enc, V, PC.Storage{l1, r1, c1, m1}), RS.rn_reply(~K, ~enc, V, PC.Counters{m2}), e))
        case PC.Storage{+l2, r2, c2, m2}: Equal.cong(PC.Reply<String, V>, PC.Reply<K, V>, r => retype(K, V, r, PC.Storage{l1, r1, c1, m1}), RS.rn_reply(~K, ~enc, V, PC.Storage{l1, r1, c1, m1}), RS.rn_reply(~K, ~enc, V, PC.Storage{l2, r2, c2, m2}), e)

def results(~K: Data, ~enc: K -> String, -V: Data, actual: D.Outcome<K, V>, expected: PC.Result<K, V>) -> Type:
  match actual expected:
    case D.Returned{c, answer, events, count} PC.Returned{s, expected_reply, expected_events, expected_count}:
      E.states(~String, ~Lookup.string_same, V, F.abstract(String, V, RM.rn_cache(~K, ~enc, V, c)), RS.rn_model(~K, ~enc, V, s)) & {R.reply(K, V, answer) == expected_reply : PC.Reply<K, V>} & {events == expected_events : List<&2, Clock.Event>} & {count == expected_count : Nat}
    case D.Failed{c, error, events, count} PC.Failed{s, expected_error, expected_events, expected_count}:
      E.states(~String, ~Lookup.string_same, V, F.abstract(String, V, RM.rn_cache(~K, ~enc, V, c)), RS.rn_model(~K, ~enc, V, s)) & {error == expected_error : Clock.Error} & {events == expected_events : List<&2, Clock.Event>} & {count == expected_count : Nat}
    case D.Returned{c, answer, events, count} PC.Failed{s, expected_error, expected_events, expected_count}: Empty
    case D.Failed{c, error, events, count} PC.Returned{s, expected_reply, expected_events, expected_count}: Empty

def outcomes(~K: Data, ~enc: K -> String, -V: Data, actual: List<&2, D.Outcome<K, V>>, expected: List<&2, PC.Result<K, V>>) -> Type:
  match actual expected:
    case Nil{} Nil{}: Unit
    case Con{o, os} Con{r, rs}: results(~K, ~enc, V, o, r) & outcomes(~K, ~enc, V, os, rs)
    case Nil{} Con{r, rs}: Empty
    case Con{o, os} Nil{}: Empty

# Final states related (canonically, through the key renaming), same unused
# provider events, same total request count, and every per-request outcome
# related to its independent K-typed result with the exact K-typed reply.
def traces(~K: Data, ~enc: K -> String, -V: Data, actual: D.Trace<K, V>, expected: Traces.Trace<K, V>) -> Type:
  match actual expected:
    case D.Ran{c, ea, os, na} Traces.Finished{s, eb, rs, nb}:
      E.states(~String, ~Lookup.string_same, V, F.abstract(String, V, RM.rn_cache(~K, ~enc, V, c)), RS.rn_model(~K, ~enc, V, s)) & {ea == eb : List<&2, Clock.Event>} & {na == nb : Nat} & outcomes(~K, ~enc, V, os, rs)

def results_transfer(~K: Data, ~enc: K -> String, ~inj: @a: K -> @b: K -> @e: {enc(a) == enc(b) : String} -> {a == b : K}, -V: Data, o: D.Outcome<K, V>, r: PC.Result<K, V>, related: R.results(~String, ~Lookup.string_same, V, RN.rn_outcome(~K, ~enc, V, o), RS.rn_result(~K, ~enc, V, r))) -> results(~K, ~enc, V, o, r):
  match o r:
    case D.Returned{c, +answer, events, count} PC.Returned{s, +expected, ee, ec}:
      (st, rp, ev, ct) = related
      (st, reply_injective(~K, ~enc, ~inj, V, R.reply(K, V, answer), expected, Equal.trans(PC.Reply<String, V>, RS.rn_reply(~K, ~enc, V, R.reply(K, V, answer)), R.reply(String, V, RN.rn_answer(~K, ~enc, V, answer)), RS.rn_reply(~K, ~enc, V, expected), Equal.sym(PC.Reply<String, V>, R.reply(String, V, RN.rn_answer(~K, ~enc, V, answer)), RS.rn_reply(~K, ~enc, V, R.reply(K, V, answer)), reply_rn(~K, ~enc, V, answer)), rp)), ev, ct)
    case D.Failed{c, error, events, count} PC.Failed{s, ex, ee, ec}: related
    case D.Returned{c, answer, events, count} PC.Failed{s, ex, ee, ec}: related
    case D.Failed{c, error, events, count} PC.Returned{s, ex, ee, ec}: related

def outcomes_transfer(~K: Data, ~enc: K -> String, ~inj: @a: K -> @b: K -> @e: {enc(a) == enc(b) : String} -> {a == b : K}, -V: Data, os: List<&2, D.Outcome<K, V>>, rs: List<&2, PC.Result<K, V>>, related: PT.outcomes(V, RN.rn_outcomes(~K, ~enc, V, os), RS.rn_results(~K, ~enc, V, rs))) -> outcomes(~K, ~enc, V, os, rs):
  match os rs:
    case Nil{} Nil{}: Unit{}
    case Con{o, os2} Con{r, rs2}:
      (head, tail) = related
      (results_transfer(~K, ~enc, ~inj, V, o, r, head), outcomes_transfer(~K, ~enc, ~inj, V, os2, rs2, tail))
    case Nil{} Con{r, rs2}: related
    case Con{o, os2} Nil{}: related

def traces_transfer(~K: Data, ~enc: K -> String, ~inj: @a: K -> @b: K -> @e: {enc(a) == enc(b) : String} -> {a == b : K}, -V: Data, actual: D.Trace<K, V>, expected: Traces.Trace<K, V>, related: PT.traces(V, RN.rn_trace(~K, ~enc, V, actual), RS.rn_strace(~K, ~enc, V, expected))) -> traces(~K, ~enc, V, actual, expected):
  match actual expected:
    case D.Ran{c, ea, os, na} Traces.Finished{s, eb, rs, nb}:
      (st, ev, ct, outs) = related
      (st, ev, ct, outcomes_transfer(~K, ~enc, ~inj, V, os, rs, outs))

def created_rel(~K: Data, ~enc: K -> String, ~same: K -> K -> Bool, -V: Data, +zero_key: K, +zero_value: V, +requests: List<&2, Pub.Request<K, V>>, +events: List<&2, Clock.Event>, actual: Result<&2, &2, String, C.Cache<K, V>>, expected: Result<&2, &2, String, S.Model<K, V>>) -> Type:
  match actual expected:
    case Fail{ea} Fail{eb}: {ea == eb : String}
    case Done{c} Done{s}: traces(~K, ~enc, V, D.run(~K, ~enc, V, requests, c, zero_key, zero_value, events), Traces.run(~K, ~same, V, commands(K, V, requests), s, zero_key, zero_value, events))
    case Fail{ea} Done{s}: Empty
    case Done{c} Fail{eb}: Empty

def lift(~K: Data, ~enc: K -> String, ~same: K -> K -> Bool, ~agree: @+a: K -> @+b: K -> {String.eq(enc(a), enc(b)) == same(a)(b) : Bool}, ~inj: @a: K -> @b: K -> @e: {enc(a) == enc(b) : String} -> {a == b : K}, -V: Data, +n: Nat, +zero_key: K, +zero_value: V, +requests: List<&2, Pub.Request<K, V>>, +events: List<&2, Clock.Event>, related: PT.traces(V, D.run(~String, ~Codec.string_encode, V, RN.rn_requests(~K, ~enc, V, requests), C.init(String, V, n), enc(zero_key), zero_value, events), Traces.run(~String, ~Lookup.string_same, V, PT.commands(V, RN.rn_requests(~K, ~enc, V, requests)), S.initial(String, V, n), enc(zero_key), zero_value, events))) -> PT.traces(V, RN.rn_trace(~K, ~enc, V, D.run(~K, ~enc, V, requests, C.init(K, V, n), zero_key, zero_value, events)), RS.rn_strace(~K, ~enc, V, Traces.run(~K, ~same, V, commands(K, V, requests), S.initial(K, V, n), zero_key, zero_value, events))):
  %RN.d_run(~K, ~enc, V, requests, C.init(K, V, n), zero_key, zero_value, events) : PT.traces(V, _, RS.rn_strace(~K, ~enc, V, Traces.run(~K, ~same, V, commands(K, V, requests), S.initial(K, V, n), zero_key, zero_value, events)))
  %RS.t_run(~K, ~enc, ~same, ~agree, V, commands(K, V, requests), S.initial(K, V, n), zero_key, zero_value, events) : PT.traces(V, D.run(~String, ~Codec.string_encode, V, RN.rn_requests(~K, ~enc, V, requests), C.init(String, V, n), enc(zero_key), zero_value, events), _)
  %commands_rn(~K, ~enc, V, requests) : PT.traces(V, D.run(~String, ~Codec.string_encode, V, RN.rn_requests(~K, ~enc, V, requests), C.init(String, V, n), enc(zero_key), zero_value, events), Traces.run(~String, ~Lookup.string_same, V, _, S.initial(String, V, n), enc(zero_key), zero_value, events))
  related

def initial(~K: Data, ~enc: K -> String, ~same: K -> K -> Bool, ~agree: @+a: K -> @+b: K -> {String.eq(enc(a), enc(b)) == same(a)(b) : Bool}, ~inj: @a: K -> @b: K -> @e: {enc(a) == enc(b) : String} -> {a == b : K}, -V: Data, +n: Nat, +zero_key: K, +zero_value: V, +requests: List<&2, Pub.Request<K, V>>, +events: List<&2, Clock.Event>, related: PT.traces(V, D.run(~String, ~Codec.string_encode, V, RN.rn_requests(~K, ~enc, V, requests), C.init(String, V, n), enc(zero_key), zero_value, events), Traces.run(~String, ~Lookup.string_same, V, PT.commands(V, RN.rn_requests(~K, ~enc, V, requests)), S.initial(String, V, n), enc(zero_key), zero_value, events))) -> traces(~K, ~enc, V, D.run(~K, ~enc, V, requests, C.init(K, V, n), zero_key, zero_value, events), Traces.run(~K, ~same, V, commands(K, V, requests), S.initial(K, V, n), zero_key, zero_value, events)):
  traces_transfer(~K, ~enc, ~inj, V, D.run(~K, ~enc, V, requests, C.init(K, V, n), zero_key, zero_value, events), Traces.run(~K, ~same, V, commands(K, V, requests), S.initial(K, V, n), zero_key, zero_value, events), lift(~K, ~enc, ~same, ~agree, ~inj, V, n, zero_key, zero_value, requests, events, related))

def construct(~K: Data, ~enc: K -> String, ~same: K -> K -> Bool, ~agree: @+a: K -> @+b: K -> {String.eq(enc(a), enc(b)) == same(a)(b) : Bool}, ~inj: @a: K -> @b: K -> @e: {enc(a) == enc(b) : String} -> {a == b : K}, -V: Data, +zero_key: K, +zero_value: V, +capacity: U32, +size: U32, +requests: List<&2, Pub.Request<K, V>>, +events: List<&2, Clock.Event>, zero: Bool, reserved: Bool, small: Bool, related: PT.created_rel(V, enc(zero_key), zero_value, RN.rn_requests(~K, ~enc, V, requests), events, C.construct(String, V, capacity, size, zero, reserved, small), S.construct(String, V, capacity, size, zero, reserved, small))) -> created_rel(~K, ~enc, ~same, V, zero_key, zero_value, requests, events, C.construct(K, V, capacity, size, zero, reserved, small), S.construct(K, V, capacity, size, zero, reserved, small)):
  match zero reserved small:
    case True{} a b: {==}
    case False{} True{} b: {==}
    case False{} False{} True{}: {==}
    case False{} False{} False{}: initial(~K, ~enc, ~same, ~agree, ~inj, V, U32.to_nat(capacity), zero_key, zero_value, requests, events, related)

# Every trace of the K-keyed public machine from construction refines the
# independent K-keyed specification trace.
def from_construction(~K: Data, ~enc: K -> String, ~same: K -> K -> Bool, ~agree: @+a: K -> @+b: K -> {String.eq(enc(a), enc(b)) == same(a)(b) : Bool}, ~inj: @a: K -> @b: K -> @e: {enc(a) == enc(b) : String} -> {a == b : K}, -V: Data, +zero_key: K, +zero_value: V, +capacity: U32, +size: U32, +requests: List<&2, Pub.Request<K, V>>, +events: List<&2, Clock.Event>) -> created_rel(~K, ~enc, ~same, V, zero_key, zero_value, requests, events, C.new_with_size(K, V, capacity, size), S.new_with_size(K, V, capacity, size)):
  construct(~K, ~enc, ~same, ~agree, ~inj, V, zero_key, zero_value, capacity, size, requests, events, U32.is_eq(capacity, 0), U32.is_eq(size, 4294967295), U32.is_lt(size, capacity), PT.from_construction(V, enc(zero_key), zero_value, capacity, size, RN.rn_requests(~K, ~enc, V, requests), events))
