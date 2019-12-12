universes u v 
variable α :Type u
structure graph  :=
(vertex : Type u)
(edge : Type v)
(φ : (edge→ vertex)× (edge→ vertex))

#check graph
#print graph

/-graph with single point and loop-/
inductive ele:Type
|p1:ele
def a (x:ele):ele:= ele.rec_on x ele.p1
def graph0:graph := {vertex:=ele,edge:=ele,φ := prod.mk a a}
#print graph0

/-graph with 2 points and an edge-/
inductive ele_2:Type
|p1:ele_2
|p2:ele_2
def b1 (x:ele):ele_2:=ele.rec_on x ele_2.p1
def b2 (x:ele):ele_2:=ele.rec_on x ele_2.p2
def graph1:graph := {vertex:=ele_2,edge:=ele,φ := prod.mk b1 b2}
#print graph1

