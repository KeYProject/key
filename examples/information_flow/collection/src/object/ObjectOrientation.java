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
    
    
    public static ObjectOrientation o0, o1, o2;
    ObjectOrientation next;
    private static ObjectOrientation high_object;
    private static boolean high;
    
    //@ separates o0, o1, o2;
    //@ also
    //@ separates \nothing \new_objects o0, o1, o2;
    public void insecure_object_assignment() {
        o0 = high_object;
    }

    /*@ normal_behavior
      @ separates \nothing \new_objects o0, o1, o2;
      @ */
    public void secure_two_object_creation() {
        o0 = new ObjectOrientation(0);
        o1 = new ObjectOrientation(1);
        o2 = o0;
    }
    
    //@ separates \nothing \new_objects o0, o1, o2;
    public void insecure_two_object_creation() {
        o0 = new ObjectOrientation(0);
        o1 = new ObjectOrientation(1);
        o2 = (high ? o0 : o1);
    }

    //@ separates \nothing \new_objects o0, o1;
    public void secure_if_two_object_creation() {
        if(high) {
            o0 = new ObjectOrientation(0);
            o1 = new ObjectOrientation(1);
        } else {
            o1 = new ObjectOrientation(1);
            o0 = new ObjectOrientation(0);
        }
    }

    //@ separates \nothing \new_objects o0, o1;
    //@ also
    // the following contract does not hold
    //@ separates \nothing \new_objects o0, o1, o1.next;
    public void if_two_object_creation_next() {
        if(high) {
            o0 = new ObjectOrientation(0);
            o1 = new ObjectOrientation(1);
            o1.next = o1;
        } else {
            o1 = new ObjectOrientation(1);
            o0 = new ObjectOrientation(0);
            o1.next = o0;
        }
    }


//--------------


    //@ separates o0, o1, o2;
    public void secure_method_call() {
        secure_two_object_creation();
        o2 = o1;
    }


//--------------

    //@ requires    \typeof(a) == \type(Object[]);
    //@ separates   a.length \erases (\seq_def int i; 0; a.length; a[i]);
    public void secure_while_i(Object[] a) {
        /*@ loop_invariant 0 <= i && i <= a.length;
            loop_invariant a != null && \typeof(a) == \type(Object[]);
            assignable a[*];
            decreases a.length - i;
            separates i, a.length, (\seq_def int j; 0; i; a[j]) \new_objects a[i-1];
          @*/
        for (int i = 0; i < a.length; i++) {
            a[i] = new Object();
        }
    }

}
