
public class System {
	/*@ normal_behavior
	  @ ensures \result == 42;
	  @*/
	public /*@ strictly_pure @*/ static int identityHashCode(Object obj);
}
