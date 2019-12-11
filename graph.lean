universes u v 
variable α :Type u
structure graph  :=
(vertex : Type u)
(edge : Type v)
(φ : (edge→ vertex)× (edge→ vertex))

#check graph
#print graph

/-graph with single point and loop-/
inductive ele:Type:=
|0
def a (x:ele):ele:= ele.rec_on x 0
def graph0:graph := {vertex:=ele,edge:=ele,φ := prod.mk a a}
#print graph0

/-graph with 2 points and an edge-/
inductive ele_2:Type:=
|0
|1
def b1 (x:ele):ele_2:=ele.rec_on x 0
def b2 (x:ele):ele_2:=ele.rec_on x 1
def graph1:graph := {vertex:=ele_2,edge:=ele,φ := prod.mk b1 b2}
#print graph1

