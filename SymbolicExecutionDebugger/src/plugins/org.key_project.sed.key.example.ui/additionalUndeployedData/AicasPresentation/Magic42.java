package example5;

public class Magic42 {
	public static int compute(int x) {
		int y = computeHelp(x);
		int res = 0;
		while (y % 2 != 0) {
			if (res % 2 == 0) {
				res = 2 * res + (y % 2);
				y = y / 2;
			} else {
				res = 2 * res;
			}
		}
		return res * 2;
	}

	public static int computeHelp(int x) {
		int y = (x >= 0 ? x : -x) / 2000;
		return 320 * y + 7;
	}
}