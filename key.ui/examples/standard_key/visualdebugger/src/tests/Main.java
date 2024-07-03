package tests;

public class Main {

	/**
	 * @param args
	 */
	/*@ public normal_behavior
	  @ requires true;
	  @ ensures true;
	  @ */
	public static void main(String[] args) {
		ClassA2 a2 = new ClassA2();
		Caller c = new Caller();
		// null instead of a2 cause exception
		System.out.println( c.callingFunction(a2));		

	}

}
