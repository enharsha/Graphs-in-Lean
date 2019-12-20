universes u v 
variable α :Type u
structure graph  :=
(vertex : Type u)
(edge : Type v)
(φ1 : (edge→ vertex))
(φ2 :(edge→ vertex))

#check graph
#print graph

/-graph with single point and loop-/
inductive One:Type
|one:One
def a (x:One):One:= One.one
def graph0:graph := {vertex:=One,edge:=One,φ1 := a,φ2:=a}
#print graph0

/-graph with 2 points and an edge-/
inductive Two:Type
|one:Two
|two:Two
def b1 (x:One):Two:=Two.one
def b2 (x:One):Two:=Two.two
def graph1:graph := {vertex:=Two,edge:=One,φ1 :=b1,φ2:= b2}
#print graph1

inductive path (g:graph)(start:g.vertex):(g.vertex) → Type u
|fix : path start 
|addedge (add:g.edge)(last:g.vertex)(p: path last)(pr:last = g.φ1 add): path (g.φ2 add) 

open path
#check path 
constant path1: path graph0 One.one One.one  
#check path1
#print path1

inductive vector (α : Type u) : nat →  Type u
| nil {} : vector 0
| cons {n : nat} (a : α) (v : vector n) : vector (nat.succ n)  
