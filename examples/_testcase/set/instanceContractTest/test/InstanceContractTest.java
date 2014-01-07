
public class InstanceContractTest {
	private int value;
	
	public int mainVoidMethod() {
		voidMethod();
		return value;
	}

	/*@ normal_behavior
	  @ ensures value == 42;
	  @*/
	public void voidMethod() {
		value = 42;
	}
	
	public int mainNoArgs() {
		return noArgs();
	}

	/*@ normal_behavior
	  @ ensures \result == 42;
	  @*/
	public int noArgs() {
		return 42;
	}
	
	public int mainResult(int x) {
		return result(x);
	}

	/*@ normal_behavior
	  @ requires x >= 0;
	  @ ensures \result == x * x;
	  @*/
	public int result(int x) {
		return x*x;
	}
	

	
	public int mainResultNotSpecified(int x) {
		return result(x);
	}

	/*@ normal_behavior
	  @ requires x >= 0;
	  @ ensures true;
	  @*/
	public int resultNotSpecified(int x) {
		return x*x;
	}
	
	public void mainExceptinalVoid(boolean x) throws Exception {
		exceptinalVoid(x);
	}

	/*@ exceptional_behavior
	  @ signals_only Exception;
	  @ signals (Exception) true;
	  @*/
	public void exceptinalVoid(boolean x) throws Exception {
		throw new Exception();
	}
	
	public void mainExceptinalUnused(boolean x) throws Exception {
		exceptinal(x);
	}
	
	public boolean mainExceptinal(boolean x) throws Exception {
		return exceptinal(x);
	}

	/*@ exceptional_behavior
	  @ signals_only Exception;
	  @ signals (Exception) true;
	  @*/
	public boolean exceptinal(boolean x) throws Exception {
		throw new Exception();
	}
	
	public void mainBooleanResultUnused(boolean x) {
		booleanResult(x);
	}

	/*@ normal_behavior
	  @ ensures \result == !x;
	  @*/
	public boolean booleanResult(boolean x) {
		return !x;
	}
	
	public void mainBooleanResultUnspecifiedUnused(boolean x) {
		booleanResultUnspecified(x);
	}

	/*@ normal_behavior
	  @ ensures true;
	  @*/
	public boolean booleanResultUnspecified(boolean x) {
		return !x;
	}
	
	public void mainExceptionalConstructor() throws Exception {
		new IntWrapper(); 
	}
	
	public int mainConstructor() {
		IntWrapper w = new IntWrapper(42);
		return w.value;
	}
	
	public int mainOnObject(IntWrapper x) {
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
