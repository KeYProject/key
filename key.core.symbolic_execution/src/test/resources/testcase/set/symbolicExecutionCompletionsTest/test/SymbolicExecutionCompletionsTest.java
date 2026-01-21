public class SymbolicExecutionCompletionsTest {
	public static int magic(int x) {
		if (x >= 0) {
			return x;
		}
		else {
			x++;
			return 42;
		}
	}
}
