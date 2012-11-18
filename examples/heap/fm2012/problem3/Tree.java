final class Tree {
    /*@ nullable @*/ Tree left; 
    /*@ nullable @*/ Tree right;
    int data;
    //@ model \seq seq;



    /*@ represents seq = \seq_concat(
      @                  (left==null? \seq_empty: left.seq), 
      @                  \seq_concat(\seq_singleton(data),
      @                  (right==null? \seq_empty: right.seq)));
      @ accessible seq: footprint \measured_by seq.length;
      @ invariant seq.length == 1+ (left==null?0:left.seq.length)+
      @                           (right==null?0:right.seq.length);
      @ invariant (\forall int i; 0 < i && i < seq.length; 
      @               (int)seq[i-1] <= (int)seq[i]);
     //@ accessible \inv: footprint \measured_by seq.length;

     /*@ model \locset footprint;
       @ represents footprint = \set_union(this.*,
       @                        \set_union(left==null? \empty: left.footprint,
       @                                 right==null? \empty: right.footprint));
       @ accessible footprint: footprint \measured_by seq.length;
       @ invariant \disjoint(this.*, left.footprint)  || left==null;
       @ invariant \disjoint(this.*, right.footprint) ||right==null;
       @ invariant \disjoint(left.footprint,right.footprint)
       @           || left==null || right==null;
       @*/

     /*@ invariant \invariant_for(left)  || left==null;
       @ invariant \invariant_for(right) || right==null;
       @ invariant left != right || left == null;
       @*/

// XXX the semantics of \seq_sub are about to change!
 
    /*@ normal_behavior
      @ requires \invariant_for(t);
      @ ensures \result != null ==> 
      @                         \result.seq == \old(t.seq[1..t.seq.length-1]);
      @ ensures \result == null ==> t.seq == \seq_singleton(t.data);
      @ nullable
      @*/
    static Tree search_tree_delete_min (Tree t) {
       Tree tt, p2, p;
       p = t.left;
       if (p == null) {
           t = t.right;
       } else {
           p2 = t; tt = p.left;
           /*@ maintaining \invariant_for(t);
             @ maintaining \invariant_for(p2) && \invariant_for(p);
             @ maintaining (\invariant_for(tt)||tt==null);
             @ maintaining p2.seq == t.seq[0..p2.seq.length-1] 
             @                 && p2.seq.length <= t.seq.length;
             @ maintaining tt == p.left;
             @ maintaining p == p2.left;
             @ maintaining p2!=null && p != null;
             @ decreasing tt==null? 0: tt.seq.length;
             @ assignable \less_than_nothing;
             @*/
           while (tt != null) {
               p2 = p; p = tt; tt = p.left;
           }
           p2.left= p.right;
       }
       return t;
    }

}
