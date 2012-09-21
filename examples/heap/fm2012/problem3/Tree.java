class Tree {
    /*@ nullable @*/ Tree left; 
    /*@ nullable @*/ Tree right;
    int data;
    //@ ghost \seq seq;
    /*@ invariant seq == \seq_concat(
      @                  (left==null? \seq_empty: left.seq), 
      @                  \seq_concat(\seq_singleton(data),
      @                  (right==null? \seq_empty: right.seq)));
      @ invariant seq.length == 1+ (left==null?0:left.seq.length)+
      @                           (right==null?0:right.seq.length);
      @ invariant (\forall int i; 0 < i && i < seq.length; 
      @               (int)seq[i-1] <= (int)seq[i]);
     //@ accessible \inv: footprint \measured_by seq.length;

     /*@ ghost \locset footprint;
       @ invariant footprint == \set_union(this.*,
       @                        \set_union(left==null? \empty: left.footprint,
       @                                 right==null? \empty: right.footprint));
       @ invariant \invariant_for(left)  || left==null;
       @ invariant \invariant_for(right) || right==null;
       @ invariant left != right || left == null;
       @ invariant \disjoint(this.*, left.footprint)  || left==null;
       @ invariant \disjoint(this.*, right.footprint) ||right==null;
       @ invariant \disjoint(left.footprint,right.footprint)
       @           || left==null || right==null;
       @*/

// XXX the semantics of \seq_sub are about to change!
 
    /*@ normal_behavior
      @ requires \invariant_for(t);
      @ requires t.seq.length >= 2;
      @ ensures \invariant_for(\result);
      @ ensures \result.seq == t.seq[1..t.seq.length-1];
      @*/
    static Tree search_tree_delete_min (Tree t) {
       Tree tt, p2, p;
       p = t.left;
       if (p == null) {
           t = t.right;
       } else {
           p2 = t; tt = p.left;
           /*@ maintaining (\invariant_for(tt)||tt==null) && \invariant_for(p2)
             @                 && \invariant_for(p);
             @ maintaining p2.seq == t.seq[0..p2.seq.length-1] 
             @                 && p2.seq.length <= t.seq.length;
             @ maintaining tt == p.left;
             @ maintaining p == p2.left;
             @ maintaining p2!=null && p != null;
             @ decreasing tt==null? 0: tt.seq.length;
             @ assignable p2.seq, \singleton(p2.footprint);
             @*/
           while (tt != null) {
               //@ set p2.seq = \seq_sub(p2.seq,1,\seq_length(p2.seq)-1);
               //@ set p2.footprint = \set_minus(p2.footprint,p.footprint);
               p2 = p; p = tt; tt = p.left;
           }
           p2.left= p.right;
       }
       return t;
    }

}
