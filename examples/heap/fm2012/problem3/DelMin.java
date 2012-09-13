class DelMin {

    
/*@ normal_behavior
  @ requires \invariant_for(t);
  @ requires t.seq.length >= 2;
  @ ensures \invariant_for(\result);
  @ ensures \result.seq == t.seq[1..t.seq.length-1];
  @*/
Tree search_tree_delete_min (Tree t) {
   Tree tt, pp, p;
   p = t.left;
   if (p == null) {
       t = t.right;
   } else {
       pp = t; tt = p.left;
       /*@ maintaining (\invariant_for(tt)||tt==null) && \invariant_for(pp) && \invariant_for(p) && \invariant_for(t);
         @ maintaining pp.seq == t.seq[0..pp.seq.length-1] && pp.seq.length <= t.seq.length;
         @ maintaining p.seq == pp.seq[0..p.seq.length-1] && p.seq.length+1==pp.seq.length;
         @ maintaining tt == p.left;
         @ maintaining p == pp.left;
         @ maintaining tt==null ==> p.data == t.seq[0];
         @ maintaining pp!=null && p != null;
         @ decreasing tt==null? 0: tt.seq.length;
         @ assignable \less_than_nothing;
         @*/
       while (tt != null) {
           pp = p; p = tt; tt = p.left;
       }
       pp.left= p.right;
       //@ set t.seq = \seq_sub(t.seq,1,t.seq.length-1);
   }
   return t;
}
}
