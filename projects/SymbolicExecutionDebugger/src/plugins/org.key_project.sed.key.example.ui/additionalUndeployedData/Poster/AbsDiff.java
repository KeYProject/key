
public class AbsDiff {
	public static int absDiff(int x, 
			                  int y) {
		int result;
		if (x < y) {
			result = y - x;
		}
		else {
			result = x - y;
		}
		return result;
	}
}
