// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//


package vacid0.redblacktree;

/**
 * A node in a red-black tree.
 * Nodes hold an integer key and a value and are either red or black.
 * This is an implementation without null references;
 * instead, the parent of the root and the children of leaves is the special node <code>NIL</code>
 * (called the &quot;sentinel&quot; in Cormen et al.).
 * @author bruns
 *
 */
public class Node {

    final static Node NIL = new Nil();
    //@ axiom NIL != null;
    //@ axiom (\forall Nil x; x == NIL);
    //@ axiom this != NIL ==> \typeof(this) == \type(Node);

    boolean isRed;
    int key;
    int value;
    
    //@ protected ghost int height;

    Node parent, left, right;
    
    /*@ protected model \seq subtree;
      @ represents subtree = \seq_concat(\seq_singleton(this), \seq_concat(left.subtree, right.subtree));
      @ accessible subtree : treeFootprint \measured_by height;
      @*/
    
    /*@ protected model \locset footprint;
      @ represents footprint = isRed, key, value, parent, left, right, height;
      @ accessible footprint : \nothing;
      @ protected model \locset treeFootprint;
      @ represents treeFootprint = footprint, left.treeFootprint, right.treeFootprint;
      @ accessible treeFootprint : \set_union(left.treeFootprint, right.treeFootprint) \measured_by height;
      @*/

    // the red-black tree properties (`high-level' invariants)
    /*@ model boolean redBlackInvariant;
      @ represents redBlackInvariant \such_that
      @        (left == NIL || left.key < key) && (right == NIL || right.key > key)
      @     && (isRed ==> !(left.isRed || right.isRed))
      @     && left.blackLeft() == right.blackRight()
      @     && (this == NIL || (left.redBlackInvariant && right.redBlackInvariant))
      @     && \invariant_for(this);
      @ accessible redBlackInvariant : treeFootprint \measured_by height;
      @*/
    

    // `low-level' invariants
    /*@ invariant parent == NIL || parent.left == this || parent.right == this;
      @ invariant key >= 0;
      @ invariant height == (left.height > right.height ? left.height : right.height)+1;
      @ invariant \disjoint(footprint, left.treeFootprint) && \disjoint(footprint, right.treeFootprint);
      @ invariant \invariant_for(left) && \invariant_for(right);
      @ accessible \inv : treeFootprint \measured_by height;
      @*/

    /*@ normal_behavior
      @ requires key >= 0;
      @ ensures parent == NIL && left == NIL && right == NIL && this.key == key && this.value == value && !isRed;
      @ ensures \fresh(footprint);
      @ accessible \nothing; 
      @ pure
      @*/
    Node (int key, int value){
        parent = NIL;
        left = NIL;
        right = NIL;
        //@ set height = 1;
        this.key = key;
        this.value = value;
    }

    private Node (){}

    //@ measured_by height;
    protected /*@ pure @*/ int blackLeft (){
        return left.blackLeft()+(left.isRed?0:1);
    }

    //@ measured_by height;
    protected /*@ pure @*/ int blackRight(){
        return right.blackRight()+(right.isRed?0:1);
    }
    
    
    // Standard method implementations (not relevant for verification)
    
    /** Nodes are considered equal if they denote the same mapping */
    public boolean equals (Object o){
        try {
            Node n = (Node)o;
            if (this == NIL){
                return (n == NIL);
            } else
            return (n!= NIL && n.key == this.key && n.value == this.value);
        } catch (Exception e) {
            return false;
        }
    }
    
    /** Queries whether the subtrees induced by the nodes are equal.
     * Stronger condition that <code>equals()</code>.
     */
    public boolean equalSubtree (Node n){
        if (this == NIL) return n == NIL;
        return equals(n) && left.equalSubtree(n.left) && right.equalSubtree(n.right);
    }
   
    public String toString(){
        if (isRed)
            return "("+key+"->"+value+")";
        else
            return "["+key+"->"+value+"]";
    }
    
    String subtreeToString(int indent){
        String sb = this.toString()+" ";
        int i = sb.length();
        sb = sb + right.subtreeToString(i+indent);
        sb = sb + spaces(i+indent);
        sb = sb + left.subtreeToString(i+indent);
        return sb;
    }
    

    private static String spaces(int i) {
        String sb = "";
        while (i-- > 0)
            sb = sb + " ";
        return sb;
    }



    /** Special node for leaves that represent an empty data set.
     * NIL is always black.
     * @author bruns
     */
    public final static class Nil extends Node {
        /*@ represents footprint = \empty;
          @ represents treeFootprint = \empty;
          @ represents subtree = \seq_empty;
          @ accessible footprint : \nothing;
          @ accessible treeFootprint : \nothing;
          @ accessible subtree : \nothing;
          @*/
        
        //@ invariant height == 0;
        
        private Nil(){
            //@ set height = 0;
            parent = this;
            left = this;
            right = this;
            isRed= false;
        }
        protected int blackLeft(){
            return 0;
        }
        protected int blackRight(){
            return 0;
        }
        public String toString(){
            return "[NIL]";
        }
        String subtreeToString(int indent){
            return toString()+"\n";
        }
    }

}
