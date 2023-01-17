
public class PrettyPrintTest {
	public static int main(int x) {
		if (x >= 0) {
			return magic();
		}
		else {
			/*@ loop_invariant x <= -1;
			  @ decreasing 0 - x;
			  @ assignable \strictly_nothing;
			  @*/
			while (x < -1) {
				x++;
			}
			return -1;
		}
	}

	/*@ normal_behavior
	  @ ensures \result == 42;
	  @*/
	private /*@ pure @*/ static int magic() {
		return 42;
	}
}
