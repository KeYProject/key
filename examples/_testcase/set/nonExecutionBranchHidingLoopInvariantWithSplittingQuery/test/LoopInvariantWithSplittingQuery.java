
public class LoopInvariantWithSplittingQuery {
	public static int main(int x) {
		/*@ loop_invariant magic(x) >= 0;
		  @ decreasing magic(x);
		  @ assignable \strictly_nothing;
		  @*/
		while (magic(x) > 0) {
			x--;
		}
		return x;
	}

	private static int magic(int x) {
		if (x == 0) {
			return 0;
		}
		else if (x >= 0) {
			return x;
		}
		else {
			return -x;
		}
	}
}
