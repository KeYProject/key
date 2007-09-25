


package java.lang;

import gnu.classpath.Configuration;
public class Object {  

    //@ public invariant memoryArea!=null; 

    public javax.realtime.ScopedMemory memoryArea;

    /** A data group for the state of this object.  This is used to
     * allow side effects on unknown variables in methods such as
     * equals, clone, and toString. It also provides a convenient way
     * to talk about "the state" of an object in assignable
     * clauses.
     */
    //@ public non_null model org.jmlspecs.lang.JMLDataGroup objectState;
    //@ represents objectState <- org.jmlspecs.lang.JMLDataGroup.IT;

    /** The Object that has a field pointing to this Object.
     * Used to specify (among other things) injectivity (see
     * the ESC/Java User's Manual).
     */
    /*@ ghost public Object owner;
      @                     in objectState;
      @*/

    /** The number of times this object has been finalized.
     */
    //@ protected ghost int objectTimesFinalized;

    /*@ public normal_behavior
      @   assignable \nothing;
      @*/
    public /*@ pure @*/ Object() {}
    

    /*@ 
      @   public normal_behavior
      @     requires this == o;
      @     ensures \result;
      @ also
      @    requires o == null;
      @    diverges false;
      @    ensures !\result;
      @ also
      @    requires o != null;
      @    diverges false;
      @    ensures \result == o.equals(this);
      @*/
    /** @preconditions true
     * @postconditions result = (self=o)
     * @modifies
     */
    public /*@ pure @*/ boolean equals(Object o) {}

    /** The Class of this object.  Needed to specify that invoking
      * getClass() on an object always produces the same result: no
      * methods include this model field in their assignable clause,
      * so no methods can alter the outcome of invoking getClass() on
      * some object.  This property is important when using ESC/Java
      * on specs that use getClass(), just knowing that getClass() is
      * pure is not enough.
      */
    //@ public model non_null Class _getClass;
    //@ public represents _getClass <- \typeof(this);

    // The value produced by hashCode() but without any side-effects.
    /*@ public normal_behavior
      @ ensures (\forall Object o; equals(o) ==> \result == o.hashValue());
      @ public pure model int hashValue();
      @*/ 

    /*@  public behavior
      @     assignable objectState; // for subclasses with benevolent side effects
      @     ensures \result == hashValue();
      @  also
      @   public normal_behavior
      @     requires \typeof(this) == \type(Object);
      @     assignable \nothing;
      @*/
    public int hashCode() {}

    //@ public model String theString;

    /*@   public normal_behavior
      @     assignable objectState;
      @     ensures \result != null;
      @     ensures \result == theString;
      @ also
      @   public normal_behavior
      @     requires \typeof(this) == \type(Object);
      @     assignable \nothing;
      @     ensures \result != null;
      @ implies_that
      @    assignable objectState;
      @    ensures \result != null;
      @*/
    public String toString() {}

    /*@ protected behavior
      @   requires objectTimesFinalized == 0 ; // FIXME && \lockset.isEmpty();
      @   assignable objectTimesFinalized, objectState;
      @   ensures objectTimesFinalized == 1;
      @   signals (Throwable) objectTimesFinalized == 1;
      @*/
    protected void finalize() throws Throwable {}
    protected Object clone() throws CloneNotSupportedException {}

    /*@ public normal_behavior
      @   ensures \result == _getClass;
      @   ensures_redundantly \result != null;
      @*/
    public final native Class getClass();
    public final void notify() throws IllegalMonitorStateException {}
    public final void notifyAll() throws IllegalMonitorStateException {}
    public final void wait()
     throws IllegalMonitorStateException, InterruptedException {}

    //@ requires ms >= 0;
    public final void wait(long ms)
     throws IllegalMonitorStateException, InterruptedException {}

    //@ requires ms >= 0 && 0 <= ns && ns < 1000000;
    public final void wait(long ms, int ns)
     throws IllegalMonitorStateException, InterruptedException {}

}
