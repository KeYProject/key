final class Tree {
    /*@ nullable @*/ Tree left; 
    /*@ nullable @*/ Tree right;
    /*@ nullable @*/ Tree parent;
    int data;
    //@ ghost \seq seq;



    // tree abstractly represented as sequence
    /*@ invariant seq == \seq_concat(
      @                  (left==null? \seq_empty: left.seq), 
      @                  \seq_concat(\seq_singleton(data),
      @                  (right==null? \seq_empty: right.seq)));
      @ invariant seq.length == 1+ (left==null?0:left.seq.length)+
      @                           (right==null?0:right.seq.length);
      @*/

    /*@ // sortedness
      @ invariant (\forall \bigint i; 0 < i && i < seq.length; 
      @               (int)seq[i-1] <= (int)seq[i]);
      @*/

     //@ accessible \inv: footprint \measured_by seq.length;

     // declare dynamic frames
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

     // define parent
     /*@ invariant left == null || left.parent == this;
       @ invariant right == null || right.parent == this;
       @*/

     /*@ invariant \invariant_for(left)  || left==null;
       @ invariant \invariant_for(right) || right==null;
       @ invariant left != right || left == null;
       @*/

// XXX the semantics of \seq_sub is about to change!
 
    /*@ normal_behavior
      @ requires t.parent == null;
      @ requires \invariant_for(t);
      @ ensures \result != null ==> 
      @                         \result.seq == \old(t.seq[1..t.seq.length-1]);
      @ ensures \result == null ==> 
      @                         \old(t.seq) == \seq_singleton(t.data);
      @ nullable
      @*/
    static Tree search_tree_delete_min (Tree t) {
       //@ ghost \seq path;
       Tree tt, p2, p;
       //@ set path = \seq_singleton(t);
       p = t.left; 
       if (p == null) {
           t = t.right; 
       } else {
           p2 = t; 
           //@ set path = \seq_concat(path,\seq_singleton(p));
           tt = p.left; 

           /*@ maintaining \invariant_for(p2) && \invariant_for(p);
             @ maintaining (\invariant_for(tt)||tt==null);
             @ maintaining p2!=null && p != null;
             @ maintaining p == p2.left && tt == p.left;
             @ maintaining (Tree)path[0] == t;
             @ maintaining (Tree)path[path.length-1] == p;
             @ maintaining (\forall \bigint i; 0 <= i && i < path.length-1;
             @                 ((Tree)path[i]).left == (Tree)path[i+1] &&
             @                 (Tree)path[i] == ((Tree)path[i+1]).parent);
             @ maintaining (\forall \bigint i; 0 <= i && i < path.length;
             @                 (Tree)path[i]!=null 
             @                  && \invariant_for((Tree)path[i]));
             @ decreasing tt==null? 0: tt.seq.length;
             @ assignable \less_than_nothing;
             @*/
           while (tt != null) {
               //@ set path = \seq_concat(path,\seq_singleton(tt));
               p2 = p; p = tt; tt = p.left; 
           }

           p2.left= p.right;
           //@ set path = \seq_sub(path,0,\seq_length(path)-2);
           //@ set p2.seq = \seq_sub(p2.seq,1,\seq_length(p2.seq)-1);

           //@ ensures \invariant_for(p2);
           //@ assignable p2.left.parent;
           { if (p2.left != null) p2.left.parent = p2; }

           /*@ maintaining \invariant_for(p2);
             @ maintaining p2 != null;
             @ maintaining p2.parent != null || p2 == t;
             @ maintaining (\forall \bigint i; 0 <= i && i < path.length-1;
             @                ((Tree)path[i]).seq == \old(((Tree)path[i]).seq));
             @ maintaining p2.seq == \old(p2.seq[1..p2.seq.length-1]);
             @ maintaining (Tree)path[0] == t;
             @ maintaining (Tree)path[path.length-1] == p2;
             @ maintaining (\forall \bigint i; 0 <= i && i < path.length-1;
             @                 ((Tree)path[i]).left == (Tree)path[i+1] &&
             @                 (Tree)path[i] == ((Tree)path[i+1]).parent);
             @ maintaining (\forall \bigint i; 0 <= i && i < path.length;
             @                 (Tree)path[i]!= null);
             @ decreasing  path.length;
             @ assignable \infinite_union(\bigint i; 0 <= i && i < path.length;
             @                            ((Tree)path[i]).seq);
             @*/
           while (p2 != t) {
               //@ set path = \seq_sub(path,0,\seq_length(path)-2);
               p2 = p2.parent;
               //@ set p2.seq = \seq_sub(p2.seq,1,\seq_length(p2.seq)-1);
               ;
           }

       }
       return t;
    }

}
