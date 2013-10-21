package java.lang;

public class Object {  

    
    /*@ public normal_behavior
      @   assignable \nothing;
      @*/
    public /*@ pure @*/ Object() {}
    

    public /*@ pure @*/ boolean equals(java.lang.Object o);
    public int hashCode();

    public java.lang.String toString();

    protected void finalize() throws java.lang.Throwable {}
    protected java.lang.Object clone() throws java.lang.CloneNotSupportedException {}

    public final void notify();
    public final void notifyAll();
    public final void wait() throws java.lang.InterruptedException;

    public final void wait(long ms) throws java.lang.InterruptedException;

    public final void wait(long ms, int ns)
	throws java.lang.InterruptedException;

}
