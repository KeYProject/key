
public class IsInstanceTest {
	private static final IsInstanceTest A = new IsInstanceTest();
	private static final IsInstanceTest B = new IsInstanceTest();
	
	/*@ requires true;
	  @ ensures true;
	  @*/
	public static int compute(IsInstanceTest obj) {
		if (obj == A) {
			return 1;
		}
		else {
			return 0;
		}
	}
}
