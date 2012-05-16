
public class TryCatchFinally {
	/*@ requires true;
	  @ ensures true;
	  @*/		
	public int tryCatchFinally(int input) {
		int result = 0;
		try {
			result = 1 / input;
		}
		catch (ArithmeticException e) {
			result = 2;
		}
		finally {
			result = result * 2;
		}
		return result;
	}
}
