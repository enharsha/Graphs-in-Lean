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
inductive ele:Type
|p1:ele
def a (x:ele):ele:= ele.rec_on x ele.p1
def graph0:graph := {vertex:=ele,edge:=ele,φ1 := a,φ2:=a}
#print graph0

/-graph with 2 points and an edge-/
inductive ele_2:Type
|p1:ele_2
|p2:ele_2
def b1 (x:ele):ele_2:=ele.rec_on x ele_2.p1
def b2 (x:ele):ele_2:=ele.rec_on x ele_2.p2
def graph1:graph := {vertex:=ele_2,edge:=ele,φ1 :=b1,φ2:= b2}
#print graph1

inductive path (g:graph)(start:g.vertex):(g.vertex)→ Type u:=
|fix : path start 
|addedge (add:g.edge)(end1:g.vertex)(p: path end1)(pr:end1 = g.φ1 add): path (g.φ2 add) 

open path
#check path 
constant path1: path graph0 ele.p1 ele.p1  
#check path1
#print path1

constant path2 : path graph1 ele_2.p1 ele_2.p1 
