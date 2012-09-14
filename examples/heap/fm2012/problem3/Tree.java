
  class Tree {
    /*@ nullable @*/ Tree left; 
    /*@ nullable @*/ Tree right;
    int data;
    /*@ ghost \seq seq;
      @ invariant seq == \seq_concat(
      @                  (left==null? \seq_empty: left.seq), 
      @                  \seq_concat(\seq_singleton(data),
      @                  (right==null? \seq_empty: right.seq)));
      @ invariant seq.length == 1+ (left==null?0:left.seq.length)+(right==null?0:right.seq.length);
      @*/

     //@ invariant (\forall int i; 0 < i && i < seq.length; (int)seq[i-1] <= (int)seq[i]);
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
       @ invariant \disjoint(left.footprint,right.footprint)||(left==null&&right==null);
       @*/
  }


