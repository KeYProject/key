
public class LoopBodyBranchClosed {
	public static int deadBody() {
		int i = 0;
		/*@ loop_invariant i == 0;
		  @ decreasing i;
		  @ assignable \strictly_nothing;
		  @*/	
		while (i > 0) {
			i--;
		}
		return i;
	}
}
