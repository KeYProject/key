
public class RecursiveFibonacci {
	/*@ requires true;
	  @ ensures true;
	  @*/
	public int fibonacci10() {
		return fibonacci(10);
	}
	
	/*@ requires true;
	  @ ensures true;
	  @*/
	public int fibonacci(int n) {
		if (n == 0) {
			return 0;
		}
		else if (n == 1) {
			return 1;
		}
		else if (n >= 2) {
			return fibonacci(n - 1) + fibonacci(n - 2);
		}
		else {
			throw new IllegalArgumentException("n is negative.");
		}
	}
}
