import data.finset
import data.fintype
import data.list.basic
import data.nat.basic

universes u v 
variable β :Type
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

structure finitegraph (β :Type):=
(fvertex: finset β )
(fedge : finset (β × β))
(is_sub: fedge ⊆ (finset.product fvertex fvertex))

def neighbor_of_set (g : finitegraph β ) (s:finset β ) (p: s ⊆ g.fvertex): finset β :=
(finset.filter (λ v, (∃ (w : β ) (h : w ∈ s), (v,w) ∈ g.fedge ∨ (w,v)∈ g.fedge)) g.fvertex) ∪ s

#check neighbor_of_set
#print neighbor_of_set

def filler (g:finitegraph nat)(s:finset nat)(p: s ⊆ g.fvertex): (neighbor_of_set g s p) ⊆ g.fvertex:=
begin intro, apply finset.union_subset (finset.filter_subset g.fvertex) (p),end

def filler2 (g:finitegraph nat)(s:finset nat)(p: s ⊆ g.fvertex): s ⊆ (neighbor_of_set g s p) := 
begin intro, apply finset.subset_union_right, end

structure connected_step(g: finitegraph nat) := 
(pr1 : finset nat)
(pr2 : pr1 ⊆ g.fvertex) 

def connected_comp (g:finitegraph nat)(s:finset nat)(p:s⊆ g.fvertex): nat → connected_step g 
| 0 := {pr1 := s, pr2:=p}
|(x+1) := {pr1:= neighbor_of_set g (connected_comp x).pr1 (connected_comp x).pr2, 
           pr2:= filler g (connected_comp x).pr1  (connected_comp x).pr2  } 

#check connected_comp
#print connected_comp

def is_connected (g:finitegraph nat)(s:finset nat)(p:s⊆ g.fvertex):= 
if (∃ n:nat, (connected_comp g s p (n+1)).pr1 = (connected_comp g s p n).pr1) then 1 else 0


