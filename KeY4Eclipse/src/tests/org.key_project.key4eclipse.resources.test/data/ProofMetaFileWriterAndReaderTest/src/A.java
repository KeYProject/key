
public class A {
	public int magic() {
		return 42;
	}
	
	/*@ normal_behavior
	  @ ensures \result == 42;
	  @*/
	public /*@ strictly_pure @*/ int contractMagic();
}
