


package java.lang;

import javax.realtime.*;

public class Object {  

    //@ public invariant memoryArea!=null && memoryArea.stack!=null; 

    public final javax.realtime.ScopedMemory memoryArea = <currentMemoryArea>;
	//	javax.realtime.ScopedMemory.currentMemoryArea;

    /*    public javax.realtime.ScopedMemory memoryArea(){
	return memoryArea;
	}*/

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

    public int hashCode() {}

    public String toString() {}

    protected void finalize() throws Throwable {}
    protected Object clone() throws CloneNotSupportedException {}

    public final native Class getClass();
    public final void notify() throws IllegalMonitorStateException {}
    public final void notifyAll() throws IllegalMonitorStateException {}
    public final void wait()
     throws IllegalMonitorStateException, InterruptedException {}

    public final void wait(long ms)
     throws IllegalMonitorStateException, InterruptedException {}

    public final void wait(long ms, int ns)
     throws IllegalMonitorStateException, InterruptedException {}

}
