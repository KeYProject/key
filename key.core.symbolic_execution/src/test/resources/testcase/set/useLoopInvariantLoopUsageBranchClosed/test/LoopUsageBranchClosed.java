
public class LoopUsageBranchClosed {
	public static int deadCodeAfterLoop() {
		int i = 2;
		/*@ loop_invariant i >= 0;
		  @ decreasing i;
		  @ assignable \strictly_nothing;
		  @*/	
		while (i >= 0) {
		}
		return i;
	}
}
