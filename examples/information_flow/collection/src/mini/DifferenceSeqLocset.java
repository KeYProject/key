/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package mini;

/**
 *
 * @author christoph
 */
public class DifferenceSeqLocset {
    public boolean b;
    public static D l1, l2, l3;
    
    //@ invariant l3 == l1 || l3 == l2;
    //@ invariant l1 != l2;
    
    /*@ normal_behavior
      @     respects    \locset(l1.b, l2.b, l3.b);
      @
      @ normal_behavior
      @     respects    l1.b, l2.b, l3.b;
      @*/
    void m() {
        if (b) {
            l3 = l1;
        } else {
            l3 = l2;
        }
    }
}

class D {
    public boolean b;
}
