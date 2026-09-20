// Clock-only reference adapter. Validation copies the pinned lru.go/cache.go to
// build/reference, changes package name, and replaces only now()'s time source.
package main
import("encoding/json";"fmt";"os";"time";"reflect";"strconv")
var tick int64
var stride int64
var reads int64
func referenceNow() int64 { v:=tick+reads*stride;reads++;return v }
type Op struct { Name string `json:"op"`; Key string `json:"key"`; Value int64 `json:"value,string"`; NS int64 `json:"ns,string"`; Now int64 `json:"now,string"`; Stride int64 `json:"stride,string"` }
type Input struct { Capacity uint32 `json:"capacity"`; Ops []Op `json:"ops"`; Seed []string `json:"seed_metrics"`; KeyType string `json:"key_type"` }
// Encode every integer as a decimal string, without a float64 intermediate.
func exact(v reflect.Value) any {
 if !v.IsValid(){return nil}
 if v.Kind()==reflect.Interface {if v.IsNil(){return nil};return exact(v.Elem())}
 switch v.Kind(){
 case reflect.Int,reflect.Int64: return strconv.FormatInt(v.Int(),10)
 case reflect.Uint,reflect.Uint32,reflect.Uint64:return strconv.FormatUint(v.Uint(),10)
 case reflect.Bool:return v.Bool()
 case reflect.String:return v.String()
 case reflect.Slice:out:=make([]any,v.Len());for i:=range out{out[i]=exact(v.Index(i))};return out
 case reflect.Map:out:=map[string]any{};iter:=v.MapRange();for iter.Next(){out[iter.Key().String()]=exact(iter.Value())};return out
 case reflect.Struct:out:=map[string]any{};for i:=0;i<v.NumField();i++{out[v.Type().Field(i).Name]=exact(v.Field(i))};return out
 default:panic("unsupported output type")
 }
}
func main(){
 var input Input;decoder:=json.NewDecoder(os.Stdin);decoder.DisallowUnknownFields();if err:=decoder.Decode(&input);err!=nil{panic(err)}
 var out []any
 switch input.KeyType {
 case "","string":out=run[string](input,func(s string)string{return s})
 case "int64":out=run[int64](input,func(s string)int64{if s==""{return 0};n,e:=strconv.ParseInt(s,10,64);if e!=nil{panic(e)};return n})
 case "uint64":out=run[uint64](input,func(s string)uint64{if s==""{return 0};n,e:=strconv.ParseUint(s,10,64);if e!=nil{panic(e)};return n})
 default:panic("unsupported key type")
 }
 if err:=json.NewEncoder(os.Stdout).Encode(exact(reflect.ValueOf(out)));err!=nil{panic(fmt.Sprint(err))}
}
// Keys arrive as decimal strings for integer key types; hashing is irrelevant
// to observable decisions, so every key uses the same constant hash.
func run[K comparable](input Input,parse func(string)K)[]any{
 c,err:=New[K,int64](input.Capacity,func(K)uint32{return 0});if err!=nil{panic(err)}
 if input.Seed!=nil {
  if len(input.Seed)!=5{panic("metric fixture")};var nums [5]uint64
  for i,s:=range input.Seed{n,e:=strconv.ParseUint(s,10,64);if e!=nil{panic(e)};nums[i]=n}
  c.metrics=Metrics{Inserts:nums[0],Evictions:nums[1],Removals:nums[2],Hits:nums[3],Misses:nums[4]}
 }
 out:=make([]any,0)
 for _,o:=range input.Ops {
  tick=o.Now;stride=o.Stride;reads=0;var result any
  switch o.Name {
  case "Add":result=c.Add(parse(o.Key),o.Value)
  case "AddWithLifetime":result=c.AddWithLifetime(parse(o.Key),o.Value,time.Duration(o.NS))
  case "Get":v,ok:=c.Get(parse(o.Key));result=[]any{v,ok}
  case "Peek":v,ok:=c.Peek(parse(o.Key));result=[]any{v,ok}
  case "GetAndRefresh":v,ok:=c.GetAndRefresh(parse(o.Key),time.Duration(o.NS));result=[]any{v,ok}
  case "Contains":result=c.Contains(parse(o.Key))
  case "Remove":result=c.Remove(parse(o.Key))
  case "RemoveOldest":k,v,ok:=c.RemoveOldest();result=[]any{k,v,ok}
  case "GetOldest":k,v,ok:=c.GetOldest();result=[]any{k,v,ok}
  case "Purge":c.Purge()
  case "PurgeExpired":c.PurgeExpired()
  case "Keys":result=c.Keys()
  case "Values":result=c.Values()
  case "Len":result=c.Len()
  case "SetLifetime":c.SetLifetime(time.Duration(o.NS))
  case "Metrics":m:=c.Metrics();m.Collisions=0;result=m
  case "ResetMetrics":m:=c.ResetMetrics();m.Collisions=0;result=m
  default:panic("unsupported operation: "+o.Name)
  }
  m:=c.Metrics();m.Collisions=0
  out=append(out,map[string]any{"result":result,"metrics":m,"len":c.Len(),"reads":reads})
 }
 return out
}
