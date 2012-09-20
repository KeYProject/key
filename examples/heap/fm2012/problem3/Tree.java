class Tree {
    /*@ nullable @*/ Tree left; 
    /*@ nullable @*/ Tree right;
    int data;
    /*@ ghost \seq seq;
      @ invariant seq == \seq_concat(
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
       @ invariant \invariant_for(left) ||left==null;
       @ invariant \invariant_for(right) ||right==null;
       @ invariant \disjoint(this.*, left.footprint) || left==null;
       @ invariant \disjoint(this.*, right.footprint) ||right==null;
       @ invariant left != right || left == null;
       @ invariant \disjoint(left.footprint,right.footprint)
       @           || (left==null&&right==null);
       @*/
 
    /*@ normal_behavior
      @ requires \invariant_for(t);
      @ requires t.seq.length >= 2;
      @ ensures \invariant_for(\result);
      @ ensures \result.seq == t.seq[1..t.seq.length-1];
      @*/
    static Tree search_tree_delete_min (Tree t) {
       Tree tt, pp, p;
       p = t.left;
       if (p == null) {
           t = t.right;
       } else {
           pp = t; tt = p.left;
           /*@ maintaining (\invariant_for(tt)||tt==null) && \invariant_for(pp)
             @                 && \invariant_for(p) && \invariant_for(t);
             @ maintaining pp.seq == t.seq[0..pp.seq.length-1] 
             @                 && pp.seq.length <= t.seq.length;
             @ maintaining p.seq == pp.seq[0..p.seq.length-1] 
             @                 && p.seq.length+1==pp.seq.length;
             @ maintaining tt == p.left;
             @ maintaining p == pp.left;
             @ maintaining tt==null ==> p.data == t.seq[0];
             @ maintaining t != null && pp!=null && p != null;
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
