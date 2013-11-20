Information flow examples.

A collection of several examples centering on the problem of low variables of object type and the creation of new objects. The collection includes the examples form the papers "A Logic for Information Flow in Object-Oriented Programs" and "From coupling relations to mated invariants for checking information flow".

The information flow proof obligations of most secure examples can be proved fully automatically using the macro "Full Information Flow Auto Pilot".


--- source code ---

public class AmtoftBanerjee {

    int q;

    //@ normal_behavior
    //@ assignable \nothing;
    //@ separates \nothing \declassifies q \erases \result;
    int getQ() {
        return this.q;
    }

    void setQ(int n) {
        this.q = n;
    }


    static int secret, z;

    //@ normal_behavior
    //@ separates \nothing \declassifies secret \erases z;
    //@ also
    // the following contract is not satisfied
    //@ normal_behavior
    //@ separates \nothing \erases z;
    static void m_1() {
        AmtoftBanerjee x1;
        AmtoftBanerjee x2 = new AmtoftBanerjee();
        x1 = x2;
        x1.setQ(secret);
        z = x2.getQ();
    }

    //@ normal_behavior
    //@ separates \nothing \erases z;
    static void m_2() {
        AmtoftBanerjee x1 = new AmtoftBanerjee();
        AmtoftBanerjee x2 = new AmtoftBanerjee();
        x1.setQ(secret);
        z = x2.getQ();
    }
}


public class AmtoftBanerjee2 {
    int marg, res;
    //@ invariant (marg != 0) ==> (res == expensive(marg));

    //@ normal_behavior
    //@ assignable marg, res;
    //@ separates z, \result;
    int cexp(int z) {
        if (z == marg && z != 0) {
            return res;
        } else {
            int result = expensive(z);
            marg = z;
            res = result;
            return result;
        }
    }

    // The accessible clause can be proved automatically, if the query treatment
    // is set to "off" and expand local queries is set to "on".
    //@ normal_behavior
    //@ ensures \result == expensive(z);
    //@ assignable \strictly_nothing;
    //@ accessible \nothing;
    //@ separates z, \result;
    //@ helper
    int expensive(int z) {
        return z;
    }
}


public class AmtoftBanerjee3 {
    int x, a, b;

    //@ requires (a % 4) == 3;
    //@ separates \nothing \declassifies x \erases b;
    void m() {
        b = x + (a % 4);
    }
}


public class Naumann {
    Node[] m_result;

    /*@ separates   x
          \erases   m_result,
                    (\seq_def int i; 0; m_result.length; m_result[i]),
                    (\seq_def int i; 0; m_result.length; m_result[i].val); */
    //@ helper
    void  Pair_m(int x, int secret) {
        /*@ normal_behavior
            ensures     m_result != null && m_result.length == 10;
            ensures     \typeof(m_result) == \type(Node[]);
            separates       \nothing
              \new_objects  m_result; */
        { m_result = new Node[10]; }
        int i = 0;
        /*@ loop_invariant 0 <= i && i <= m_result.length;
            loop_invariant m_result != null && \typeof(m_result) == \type(Node[]);
            assignable  m_result[*];
            decreases   m_result.length - i;
            separates       i, x,
                            m_result,
                            (\seq_def int j; 0; i; m_result[j]),
                            (\seq_def int j; 0; i; m_result[j].val)
              \new_objects  m_result[i-1];
          @*/
        while (i < 10) {
            m_result[i] = new Node();
            m_result[i].val = x;
            i++;
        }
    }

    class Node {
        public int val;
    }

}


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
