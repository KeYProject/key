package object;

/*
 * To change this template, choose Tools | Templates and open the template in
 * the editor.
 */



/**
 *
 * @author christoph
 */
public final class ObjectOrientation {
    int i;

    
    public ObjectOrientation(int i) {
        this.i = i;
    }

    
//--------------

    
    //@ separates \nothing \new_objects \result;
    public ObjectOrientation secure_object_creation() {
        return new ObjectOrientation(1);
    }

    //@ separates \nothing \erases \result.i;
    public ObjectOrientation secure_object_creation_2() {
        return new ObjectOrientation(1);
    }
    
    //@ separates \nothing \erases \result.i \new_objects \result;
    public ObjectOrientation secure_object_creation_3() {
        return new ObjectOrientation(1);
    }
    
    
//--------------
    
    
    public static ObjectOrientation a0, a1, a2;
    private static boolean high;
    
    //@ separates \nothing \new_objects a0, a1, a2;
    public void secure_two_object_creation() {
        a0 = new ObjectOrientation(0);
        a1 = new ObjectOrientation(1);
        a2 = a0;
    }
    
    //@ separates \nothing \new_objects a0, a1, a2;
    public void insecure_two_object_creation() {
        a0 = new ObjectOrientation(0);
        a1 = new ObjectOrientation(1);
        a2 = (high ? a0 : a1);
    }
}
