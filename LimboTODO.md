# Limbo TODO #

  * + to concat arrays

  * [.md](.md) for tuples

  * arbitrary precision integers arithmetics (using libmp, already part of Inferno)

  * multiline comments `/* */` or other ?

  * FFI to hosts .dll/.so (via driver?)

  * PCRE module

  * possibility to declare array of int16 and float32 (Dis supports conversion to/from the types)

  * library of collection `(SortedArray, SortedMap, SortedSet, HashMap, HashSet, SkipList, Judy, ...)` and useful types `(Complex, Rational, Matrix, ...)`

  * nested functions, closures

  * lock-free structures (at least a dictionary)

  * 'deriving' from Haskell
```
Picid : adt deriving (eq, show)
{
	x, y : int; 
}
```
> will produce:
```
Picid : adt
{
	x, y : int;
	eq : fn(a:self ref Picid, b:ref Picid) : int;
	show : fn(a:self ref Picid) : string;
};
Picid.eq(a:self ref Picid, b:ref Picid) : int 
{
	return a.x==b.x && a.y==b.y; 
}
Picid.show(a:self ref Picid) : string
{
	return "{x="+string a.x+",y="+string a.y+"}";
}
```
  * 'eq' for build-in types (as well as for arrays and tuples) to allow them be used in functions like lists->ismember() where template parameter require 'eq'
```
wetest : list of int = nil;
sys->print("%d\n", lists->ismember(666,wetest));
```

  * this works:
```
wetest : list of ref Picid = nil;
picid := ref Picid(x, y);
sys->print("%d\n", lists->ismember(picid,wetest));
```
> but this does not work:
```
wetest : list of Picid = nil;
picid := Picid(x, y);
sys->print("%d\n", lists->ismember(picid,wetest));
```