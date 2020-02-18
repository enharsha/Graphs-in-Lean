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

inductive path (g:graph.{u v})(start:g.vertex):(g.vertex) → Type (max u v)
|fix{} : path start 
|addedge (add:g.edge)(last:g.vertex)(p: path last)(pr:last = g.φ1 add): path (g.φ2 add) 

#check path 
#check path.addedge

/-path with single point-/
def path0 : path graph0 One.one One.one:= path.fix
/-path with one edge-/
def path1a : path graph1 Two.one Two.one:= path.fix 
def path1b : path graph1 Two.one Two.two := path.addedge One.one Two.one path1a rfl
#check path1b
#print path1b

def neighbor (g:graph.{u v})(w:g.vertex) : g.vertex → bool:= λ s: g.vertex, if ((∃ e1:g.edge,g.φ1 e1 = s) ∨ (∃ e2: g.edge, g.φ2 e2 = s)) then 1 else 0
/-neighbor of a vertex-/
#check neighbor
#print neighbor

structure finitegraph (fvertex: Type)[fintype fvertex] (fedge: Type)[fintype fedge] :=
(φ1 :(fedge→ fvertex))
(φ2 :(fedge→ fvertex))

def neighbor_of_set (g:graph.{u v})(f: g.vertex→ bool):g.vertex → bool:=sorry
/-neighbor of a set of vertices-/

def connected_comp (g: graph )(f:g.vertex→ bool) : (g.vertex → bool):= if (neighbor_of_set g f = f) then f else (connected_comp (neighbor_of_set g f))
