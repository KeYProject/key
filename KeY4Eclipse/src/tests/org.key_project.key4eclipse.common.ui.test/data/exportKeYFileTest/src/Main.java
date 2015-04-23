
public class Main {
	private a.A a;
	private b.B b;
	private c.C c;
	
	/*@ normal_behavior
	  @ ensures \result == 42;
	  @*/
	public static int magic() {
		return 666;
	}
}
