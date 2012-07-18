
public class JDTMethodToKeYProgramMethodTest {
	public int doSomething(int a, byte b, long l, short s, Object o, String string, InnerClass ic, int[] ia, Object[][] oa) {
		return 42;
	}
	
	public static class InnerClass {
		public void run(int a, byte b, long l, short s, Object o, String string, JDTMethodToKeYProgramMethodTest test, int[] ia, Object[][] oa) {
		}
	}
}
