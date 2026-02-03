import universe.qual.Rep;
import universe.qual.Peer;
import universe.qual.Payload;

class Client {
    /*@ normal_behaviour
     @ requires t1 != t2;
     @ requires t2.isConst(0);
     @ requires \invariant_for(t1) && \invariant_for(t2);
     @ ensures t2.isConst(0);
     */
    void increment(@Rep Tree t1, @Rep Tree t2) {
        t1.increment();
    }

    /*@ normal_behaviour
     @ requires t1 != t2;
     @ requires t2.isConst(t2.value);
     @ requires \invariant_for(t1);
     @ requires \invariant_for(t2);
     @ requires t1.isConst(t1.value);
     @ ensures t1.value == \old(t1.value) + 1;
     @ ensures t1.isConst(t1.value);
     @ ensures t2.isConst(\old(t2.value));
     */
    void increment2(@Rep Tree t1, @Rep Tree t2) {
        t1.increment();
    }

    /*@ normal_behaviour
     @ requires t1 != t2;
     @ requires t2.isConst(t2.value);
     @ requires \invariant_for(t2);
     @ requires \invariant_for(t1);
     @ ensures t1.contains(value);
     @ ensures t2.isConst(\old(t2.value));
     */
    void append(@Rep Tree t1, int value, @Rep Tree t2) {
        t1.append(value);
    }

    /*@ normal_behaviour
     @ requires t1 != t2;
     @ requires t2.isConst(t2.value);
     @ requires \invariant_for(t2);
     @ requires \invariant_for(t1);
     @ requires t1.contains(0);
     @ ensures t1.contains(1);
     @ ensures t2.isConst(\old(t2.value));
     */
    void append(@Rep Tree t1, @Rep Tree t2) {
        t1.increment();
    }
}

final class Tree {
    public @Rep /*@ nullable */ Tree left;
    public @Rep /*@ nullable */ Tree right;
    public int value;

    //@ public ghost \dl_tree t;
    //@ public accessible \inv: \dl_createdRepfp(this);
    //@ public invariant t == \dl_Node(left == null ? \dl_Leaf() : left.t, value, right == null ? \dl_Leaf() : right.t);
    //@ public invariant \dl_tree_count(t) >= 0;
    //@ public invariant left != null ==> \invariant_for(left);
    //@ public invariant right != null ==> \invariant_for(right);
    //@ public invariant left != null && right != null ==> right != left; 

    /*@ public normal_behaviour
      @ ensures left == null && right == null && value == v;
      @ ensures t == \dl_Node(\dl_Leaf(), v, \dl_Leaf());
      @*/
    public /*@ pure */ Tree(int v) {
        left = null;
        right = null;
        value = v;
        //@ set t = \dl_Node(\dl_Leaf(), v, \dl_Leaf());
    }

    /*@ public normal_behaviour
      @ ensures \result == \dl_tree_is_const(t, v);
      @ measured_by \dl_tree_count(t);
      @ accessible \dl_createdRepfp(this);
      @*/
    public /*@ pure */ boolean isConst(int v) {
        if (value != v) return false;
        if (left != null && !left.isConst(v)) return false;
        if (right != null && !right.isConst(v)) return false;
        return true;
    }

    /*@ public normal_behaviour
      @ ensures \result == \dl_tree_contains(t, v);
      @ measured_by \dl_tree_count(t);
      @ accessible \dl_createdRepfp(this);
      @*/
    public /*@ pure */ boolean contains(int v) {
        if (value == v) return true;
        if (left != null && left.contains(v)) return true;
        if (right != null && right.contains(v)) return true;
        return false;
    }

    /*@ public normal_behaviour
      @ ensures t == \dl_tree_append(\old(t), v);
      @ ensures \dl_tree_count(t) == \dl_tree_count(\old(t)) + 1;
      @ measured_by \dl_tree_count(t);
      @ assignable \dl_createdRepfp(this);
      @*/
    public void append(int v) {
        if (v <= value) {
            if (left == null) {
                left = new @Rep Tree(v);
            } else {
                left.append(v);
            }
        } else {
            if (right == null) {
                right = new @Rep Tree(v);
            } else {
                right.append(v);
            }
        }
        
        //@ set t = \dl_Node(left == null ? \dl_Leaf() : left.t, value, right == null ? \dl_Leaf() : right.t);
    }

    /*@ public normal_behaviour
      @ ensures t == \dl_tree_increment(\old(t));
      @ ensures \dl_tree_count(t) == \dl_tree_count(\old(t));
      @ measured_by \dl_tree_count(t);
      @ assignable \dl_createdRepfp(this);
      @*/
    public void increment() {
        value++;
        if (left != null) left.increment();
        if (right != null) right.increment();

        //@ set t = \dl_Node(left == null ? \dl_Leaf() : left.t, value, right == null ? \dl_Leaf() : right.t);
    }
}
