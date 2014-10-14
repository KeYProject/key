package example5;

public class Number2 {
	private int content;
	private int cnt;

	public boolean equals(Number2 n) {
		if (content == n.content) {
//			int x = 0;
//			x = 1;
//			x = 2;
//			x = 3;
//			x = 4;
//			x = 5;
//			x = 6;
//			x = 7;
//			x = 8;
//			return true;
			return test(true);
		}
		else {
			return test(false);
//			return testCopy(false);
//			return test3(5);
		}
	}
	
	private boolean test(boolean met) {
		int EINWIRKLICHSEHRLANGERNAMEEINWIRKLICHSEHRLANGERNAME2 = content;
		boolean b = test2(EINWIRKLICHSEHRLANGERNAMEEINWIRKLICHSEHRLANGERNAME2);
//		boolean b = met ? test2(EINWIRKLICHSEHRLANGERNAME) : test3(EINWIRKLICHSEHRLANGERNAME); 
		return b;
	}
	
	private boolean testCopy(boolean met) {
		int j = 5;
		boolean b;
//		b = EINWIRKLICHSEHRLANGERNAMEEINWIRKLICHSEHRLANGERNAME(j);
		j = test4(j);
		b = j > 1;
//		boolean b = met ? test2(EINWIRKLICHSEHRLANGERNAME) : test3(EINWIRKLICHSEHRLANGERNAME); 
		return b;
	}
	
	private boolean test2(int x) {
		if(x == cnt) {
//			if(cnt > 1)
//				return true;
//			else
//				return false;
			return true;
		}
		else {
//			if(x > cnt)
//				return true;
//			else
//				return false;
			return false;
		}
	}
	
	private boolean test3(int x) {
		return x == cnt;
	}
	
	private int test4(int x) {
		if(x > cnt) {
			return 0;
		}
		else if(x < cnt) {
			return 1;
		}
		else if(x == cnt)
			return 2;
		
		return -1;
	}
	
	private boolean EINWIRKLICHSEHRLANGERNAMEEINWIRKLICHSEHRLANGERNAME(int x) {
		if(x == cnt) {
			return true;
		}
		else {
			return false;
		}
	}
}
