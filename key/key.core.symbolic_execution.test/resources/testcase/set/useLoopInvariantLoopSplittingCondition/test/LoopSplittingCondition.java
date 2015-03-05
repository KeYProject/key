
public class LoopSplittingCondition {
	public static int main(int x) {
		int i = x >= 0 ? x : -x;
		/*@ loop_invariant i >= 0;
		  @ decreasing i;
		  @ assignable \strictly_nothing;
		  @*/
		while (goOn(x)) {
			if (i >= 0) {
				x--;
			}
			else {
				x++;
			}
			i--;
		}
		return i;
	}

	private static boolean goOn(int x) {
		if (x > 0) {
			return true;
		}
		else {
			return false;
		}
	}
}
