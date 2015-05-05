
public class ClassWithoutPackage {
	/*@ normal_behavior
	  @ ensures \result == 42;
	  @ also
	  @ ensures \result == 42;
	  @*/
	public int m() {
		return 42;
	}
	
	/*@ normal_behavior
	  @ ensures \result == 42;
	  @ also
	  @ exceptional_behavior
	  @ signals (Exception e) true;
	  @*/
	public int n() {
		return 42;
	}
}
