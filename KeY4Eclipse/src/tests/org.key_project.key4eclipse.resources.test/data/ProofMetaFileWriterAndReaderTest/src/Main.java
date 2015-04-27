
public class Main {
	/*@ normal_behavior
	  @ requires \invariant_for(a);
	  @ ensures \result == 42 + 42 + 42;
	  @*/
	public /*@ strictly_pure @*/ static int magic(A a) {
		int first = a.magic();
		int second = a.contractMagic();
		int third = System.identityHashCode(a);
		return first + second + third;
	}
}
