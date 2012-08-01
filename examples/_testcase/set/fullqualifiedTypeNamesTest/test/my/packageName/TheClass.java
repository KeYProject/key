package my.packageName;

import my.packageName.sub.AnotherClass;


public class TheClass {
	/*@ requires true;
	  @ ensures true;
	  @*/
	public int complicatedMethod(TheInnerClass i, int a, boolean b, String x, Object[] o, AnotherClass ac, AnotherClass[] acArray) {
		return 42;
	}
	
	public class TheInnerClass {
		public int complicatedInnerMethod(TheClass z, int a, boolean b, String x, Object[] o, AnotherClass ac) {
			return 42;
		}
	}
}
