package vacid0.redblacktree;

/**
 * A node in a red-black tree.
 * Nodes hold an integer key and a value and are either red or black.
 * @author bruns
 *
 */
class Node {

    final static Node NIL = new Nil();

    boolean isRed;
    final int key;
    int value;
    
    //@ ghost int height;

    Node parent, left, right;

    // the red-black tree properties
    //@ public invariant isRed ==> !(left.isRed || right.isRed);
    //@ public invariant left.blackLeft() == right.blackRight();
    
    //@ invariant this == NIL || height == (left.height > right.height ? left.height : right.height)+1;

    Node (int key, int value){
        parent = NIL;
        left = NIL;
        right = NIL;
        this.key = key;
        this.value = value;
    }
    
    //@ helper
    private Node(){
        key = -1;
    }

    //@ measured_by height;
    protected /*@ pure helper @*/ int blackLeft (){
        return left.blackLeft()+(left.isRed?0:1);
    }

    //@ measured_by height;
    protected /*@ pure helper @*/ int blackRight(){
        return right.blackRight()+(right.isRed?0:1);
    }
   

    /*@ normal_behavior
      @   requires this != NIL;
      @   ensures true;
      @*/
    /*@ helper @*/ void leftRotate (RedBlackTree t){
        Node y = right;
        Node p = parent;
        if (y != NIL) {
            //@ set y.height = height;
            //@ set height = height -1;
            y.parent = p;
            right = y.left;
            y.left = this;

            if (p == null){
                t.setRoot(y); 
            } else {
                if (p.left == this)
                    p.left = y;
                else p.right = y;
            }
        }
    }

    //@ requires this != NIL;
    /*@ helper @*/ void rightRotate (RedBlackTree t){
        Node y = left;
        Node p = parent;
        if (y != NIL){
            //@ set y.height = height;
            //@ set height = height -1;
            y.parent = p;
            left = y.right;
            y.right = this;
            if (p == null)
                t.setRoot(y);
            else
                if (p.left == this)
                    p.left = y;
                else p.right = y;
        }
    }
    

    /** Special node for leaves that represent an empty data set.
     * NIL is always black.
     * @author bruns
     */
    public final static class Nil extends Node {
        private Nil(){
            super();
            left = this;
            right = this;
            isRed=false;
            //@ set height = 0;
        }
        protected int blackLeft(){
            return 0;
        }
        protected int blackRight(){
            return 0;
        }
    }

}
