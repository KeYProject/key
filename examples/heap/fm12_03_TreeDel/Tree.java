final class Tree {

    /*@ nullable @*/ Tree left; 
    /*@ nullable @*/ Tree right;
    int data;

    //@ ghost instance int height;

    /*@ model_behavior 
          requires treeInv();
          ensures true;
          accessible footprint();
          measured_by height;
          helper model \locset footprint() {
             return \set_union(
               this.*,
               \set_union(
                  left == null? \empty: left.footprint(), 
                  right == null? \empty: right.footprint()
               )
             );
          } @*/

    /*@ model_behavior 
          requires true;
          ensures true;
          accessible footprint();
          measured_by height;
          helper model boolean treeInv() {
             return (
                    (left != right || left == null || right == null)
                 && height >= 0
                 && (left==null || (   \disjoint(this.*, left.footprint())
                          && left.treeInv() && height > left.height))  
                 && (right==null || (   \disjoint(this.*, right.footprint())
                          && right.treeInv() && height > right.height))
                 && (left==null || right==null || \disjoint(left.footprint(), right.footprint()))) ;
          } @*/

    /*@ model_behavior 
          requires treeInv();
          ensures true;
          accessible footprint();
          measured_by height;
          helper model \seq treeRep() {
             return \seq_concat(
               (left==null) ? \seq_empty: left.treeRep(),
               \seq_concat(
                  \seq_singleton(this),
                  (right==null) ? \seq_empty: right.treeRep()
               )
             );
          } @*/


    /*@ model_behavior 
          requires treeInvUntilLeft(t) && t.treeInv();
          ensures true;
          accessible footprintUntilLeft(t);
          measured_by height;
          helper model \locset footprintUntilLeft(Tree t) {
             return (
               this == t ? \empty : \set_union(
                 this.*,
                 \set_union(
                    (left==null) ? \empty : left.footprintUntilLeft(t),
                    (right==null) ? \empty : right.footprint()
                 )
               )
             );
          } @*/


    /*@ model_behavior 
          requires true;
          ensures true;
          accessible footprintUntilLeft(t);
          measured_by height;
          helper model boolean treeInvUntilLeft(Tree t) {
             return (t == this || 
                      ( height >= 0
                     && (left != right || left == null || right == null)
                     && (right==null ||
                       (\disjoint(this.*, right.footprint())
                       && height > right.height && right.treeInv()))
                     && (left==null ||
                          (\disjoint(this.*, left.footprintUntilLeft(t))
                          && height > left.height && left.treeInvUntilLeft(t)))  
                     && (left==null || right==null ||
                          \disjoint(left.footprintUntilLeft(t), right.footprint()))
                      )
                    );
          } @*/


    /*@ model_behavior 
          requires treeInvUntilLeft(t) && t.treeInv();
          ensures true;
          accessible footprintUntilLeft(t);
          measured_by height;
          helper model \seq treeRepUntilLeft(Tree t) {
            return (
                (this == t) ? \seq_empty : 
                \seq_concat(
                  (left == null) ? \seq_empty : left.treeRepUntilLeft(t), 
                  \seq_concat(
                     \seq_singleton(this),
                     (right == null) ? \seq_empty : right.treeRep()
                  )
                )
            );
          } @*/

    
    /*@ model_behavior
          requires treeInvUntilLeft(t) && t.treeInv(); 
          requires \disjoint(footprintUntilLeft(t), t.footprint());
          ensures \result ==> (t.left == null || leftSubTree(t.left));
          ensures \result ==> (treeRep() == \seq_concat(t.treeRep(), treeRepUntilLeft(t)));
          ensures \result ==> (footprint() == \set_union(footprintUntilLeft(t), t.footprint()));
          ensures \result ==> (treeInv() <==> (treeInvUntilLeft(t) && t.treeInv()));
          ensures \result ==> (t.left == null ||
             (treeRepUntilLeft(t.left) ==
                \seq_concat(
                  \seq_singleton(t),
                  \seq_concat((t.right == null) ? \seq_empty : t.right.treeRep(), treeRepUntilLeft(t))
                )
              )
          );
          ensures \result ==> (t.left == null || 
              (footprintUntilLeft(t.left) == 
                \set_union(t.*,
                  \set_union(
                     (t.right == null) ? \empty : t.right.footprint(),
                     footprintUntilLeft(t)
                  )
                )
              )
          );
          accessible footprintUntilLeft(t);
          measured_by height;
          helper model boolean leftSubTree(Tree t) {
            return (
              t == this ||
              (left != null && left.leftSubTree(t))
            ); 
          }
      @*/

     //@ invariant true;
     //@ accessible \inv : \nothing;

    /*@ normal_behavior
      @ requires t.treeInv();
      @ ensures \result == null ==> \old(t.treeRep() == \seq_singleton(t));
      @ ensures \result != null ==> (\result.treeInv() &&
          (\exists Tree p;
              \old(t.treeRep()) == \seq_concat(\seq_singleton(p), \result.treeRep())
          ));
      @ assignable t.footprint();
      @*/
    static /*@ helper nullable @*/ Tree deleteMin (Tree t) {
       Tree tt, p2, p;

       p = t.left;
       if (p == null) {
           t = t.right;
       } else {
           p2 = t; tt = p.left;

           /*@ loop_invariant t.treeInv();
             @ loop_invariant t.treeInvUntilLeft(p2);
             @ loop_invariant p != null;
             @ loop_invariant p2 != null;
             @ loop_invariant p2.treeInv();
             @ loop_invariant p.left == tt;
             @ loop_invariant p2.left == p;
             @ loop_invariant t.leftSubTree(p2);
             // These two are actually redundant (I am almost sure)
             // @ loop_invariant t.treeRep() == \seq_concat(p2.treeRep(), t.treeRepUntilLeft(p2));
             // @ loop_invariant t.footprint() == \set_union(t.footprintUntilLeft(p2), p2.footprint());
             @ loop_invariant \disjoint(t.footprintUntilLeft(p2), p2.footprint());
             @ decreasing tt == null ? 0 : tt.height;
             @ assignable \less_than_nothing;
             @*/
           while (tt != null) {
               p2 = p; p = tt; tt = p.left;
           }
           p2.left = p.right;
       }
       return t;
    }

}
