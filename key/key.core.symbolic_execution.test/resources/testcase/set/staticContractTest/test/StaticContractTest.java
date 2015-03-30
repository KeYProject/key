
public class StaticContractTest {
	private static int value;
	
	public static int mainVoidMethod() {
		voidMethod();
		return value;
	}

	/*@ normal_behavior
	  @ ensures value == 42;
	  @*/
	public static void voidMethod() {
		value = 42;
	}
	
	public static int mainNoArgs() {
		return noArgs();
	}

	/*@ normal_behavior
	  @ ensures \result == 42;
	  @*/
	public static int noArgs() {
		return 42;
	}
	
	public static int mainResult(int x) {
		return result(x);
	}

	/*@ normal_behavior
	  @ requires x >= 0;
	  @ ensures \result == x * x;
	  @*/
	public static int result(int x) {
		return x*x;
	}
	

	
	public static int mainResultNotSpecified(int x) {
		return result(x);
	}

	/*@ normal_behavior
	  @ requires x >= 0;
	  @ ensures true;
	  @*/
	public static int resultNotSpecified(int x) {
		return x*x;
	}
	
	public static void mainExceptinalVoid(boolean x) throws Exception {
		exceptinalVoid(x);
	}

	/*@ exceptional_behavior
	  @ signals_only Exception;
	  @ signals (Exception) true;
	  @*/
	public static void exceptinalVoid(boolean x) throws Exception {
		throw new Exception();
	}
	
	public static void mainExceptinalUnused(boolean x) throws Exception {
		exceptinal(x);
	}
	
	public static boolean mainExceptinal(boolean x) throws Exception {
		return exceptinal(x);
	}

	/*@ exceptional_behavior
	  @ signals_only Exception;
	  @ signals (Exception) true;
	  @*/
	public static boolean exceptinal(boolean x) throws Exception {
		throw new Exception();
	}
	
	public static void mainBooleanResultUnused(boolean x) {
		booleanResult(x);
	}

	/*@ normal_behavior
	  @ ensures \result == !x;
	  @*/
	public static boolean booleanResult(boolean x) {
		return !x;
	}
	
	public static void mainBooleanResultUnspecifiedUnused(boolean x) {
		booleanResultUnspecified(x);
	}

	/*@ normal_behavior
	  @ ensures true;
	  @*/
	public static boolean booleanResultUnspecified(boolean x) {
		return !x;
	}
	
	public static void mainExceptionalConstructor() throws Exception {
		new IntWrapper(); 
	}
	
	public static int mainConstructor() {
		IntWrapper w = new IntWrapper(42);
		return w.value;
	}
	
	public static int mainOnObject(IntWrapper x) {
		return x.getValue();
	}
	
	public static class IntWrapper {
		public int value;

		/*@ exceptional_behavior
		  @ signals_only Exception;
		  @ signals (Exception e) true;
		  @*/
		public IntWrapper() throws Exception {
		}
		
		/*@ normal_behavior
		  @ ensures this.value == value;
		  @*/
		public IntWrapper(int value) {
			this.value = value;
		}
		
		/*@ normal_behavior
		  @ ensures \result == value;
		  @*/
		public int getValue() {
			return value;
		}
	}
}
