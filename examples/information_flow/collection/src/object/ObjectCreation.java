package object;

/*
 * To change this template, choose Tools | Templates and open the template in
 * the editor.
 */



/**
 *
 * @author christoph
 */
public final class ObjectCreation {
    int i;

    
    public ObjectCreation(int i) {
        this.i = i;
    }

    
//--------------

    
    //@ respects    \result.i;
    public ObjectCreation secure_1() {
        return new ObjectCreation(1);
    }
    
    //@ respects    \result, \result.i;
    public ObjectCreation insecure_1() {
        return new ObjectCreation(1);
    }
    
    
//--------------
    
    
    public static ObjectCreation a0, a1, a2;
    private static boolean high;
    
    /*@ respects        a0, a1, a2;
//      @ new_elems_equal a0, a1;
      @*/
    public void secure_2() {
        a0 = new ObjectCreation(0);
        a1 = new ObjectCreation(1);
        a2 = a0;
    }
    
    /*@ respects        a0, a1, a2;
//      @ new_elems_equal a0, a1;
      @*/
    public void insecure_2() {
        a0 = new ObjectCreation(0);
        a1 = new ObjectCreation(1);
        a2 = (high ? a0 : a1);
    }
}
