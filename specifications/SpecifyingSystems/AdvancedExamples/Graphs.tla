------------------------------- MODULE Graphs ------------------------------- 
LOCAL INSTANCE Naturals
LOCAL INSTANCE Sequences

IsDirectedGraph(G) ≜
   ∧ G = [node ↦ G.node, edge ↦ G.edge]
   ∧ G.edge ⊆ (G.node × G.node)

DirectedSubgraph(G) ≜    
  {H ∈ [node : SUBSET G.node, edge : SUBSET (G.node × G.node)] :
     IsDirectedGraph(H) ∧ H.edge ⊆ G.edge}
-----------------------------------------------------------------------------
IsUndirectedGraph(G) ≜
   ∧ IsDirectedGraph(G)
   ∧ ∀ e ∈ G.edge : ⟨e[2], e[1]⟩ ∈ G.edge

UndirectedSubgraph(G) ≜ {H ∈ DirectedSubgraph(G) : IsUndirectedGraph(H)}
-----------------------------------------------------------------------------
Path(G) ≜ {p ∈ Seq(G.node) :
             ∧ p ≠ ⟨ ⟩
             ∧ ∀ i ∈ 1‥(Len(p)-1) : ⟨p[i], p[i+1]⟩ ∈ G.edge}

AreConnectedIn(m, n, G) ≜ 
  ∃ p ∈ Path(G) : (p[1] = m) ∧ (p[Len(p)] = n)

IsStronglyConnected(G) ≜ 
  ∀ m, n ∈ G.node : AreConnectedIn(m, n, G) 
-----------------------------------------------------------------------------
IsTreeWithRoot(G, r) ≜
  ∧ IsDirectedGraph(G)
  ∧ ∀ e ∈ G.edge : ∧ e[1] ≠ r
                   ∧ ∀ f ∈ G.edge : (e[1] = f[1]) ⇒ (e = f)
  ∧ ∀ n ∈ G.node : AreConnectedIn(n, r, G)
=============================================================================