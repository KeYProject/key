package ex02_NOT_IN_USE;
// http://www.gzg.fn.bw.schule.de/inform/Java/Aufg03.htm#AEAckermann1
	
public class FizzBuzz {
	/*@ requires fizz != 0 && buzz != 0 && end >= 1 && System.out != null;
	  @ ensures true;
	  @*/
	public static void fizzBuzz(int fizz, 
			                    int buzz, 
			                    int end) {
		/*@ loop_invariant i >= 1 && i <= end + 1;
		  @ decreasing end + 1 - i;
		  @ assignable i;
		  @*/
		for (int i = 1; i <= end; i++) {
			if (i % fizz == 0 && i % buzz == 0) { 
				System.out.println("FizzAndBuzz");
			}
			if (i % fizz == 0) { // else if
				System.out.println("Fizz");
			}
			if (i % buzz == 0) { // else if
				System.out.println("Buzz");
			}
			else {
				System.out.println(i);
			}
		}
	}
	
	public static void main(String[] args) {
		fizzBuzz(5, 7, 50);
	}
}
