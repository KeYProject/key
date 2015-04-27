
public class CounterExample {
	/*@ normal_behavior
	  @ ensures \result == 1;
	  @*/
	public static int magic(int x) {
		if (x >= 0) {
			return 1;
		}
		else {
			return -2;
		}
	}
}
