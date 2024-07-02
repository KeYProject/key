
public class StaticMethodCall {
	/* Start
	 * main() @ StaticMethodCall
	 * doSomething();
	 * doSomething @ StaticMethodCall
	 * return @ return of doSomething
	 * int x = sub() + sub();
	 * sub() @ StaticMethodCall
	 * return subSub() + 2;
	 * subSub() @ StaticMethodCall
	 * return 2;
	 * return 2  @ return of subSub()
	 * return 4 @ return of sub()
	 * sub() @ StaticMethodCall
	 * return subSub() + 2;
	 * subSub()
	 * return 2;
	 * return 2 @ return of subSub()
	 * return 4 @ return of sub()
	 * return x;
	 * return 8 @ return of main()
	 * <endNode>
	 */
	
	/*@ requires true;
	  @ ensures true;
	  @*/	
	public static int main() {
		doSomething();
		int x = sub() + sub();
		return x;
	}
	
	public static void doSomething() {
	}
	
	public static int sub() {
		return subSub() + 2;
	}
	
	public static int subSub() {
		return 2;
	}
}
