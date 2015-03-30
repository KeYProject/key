package eval_order_access4;

public class Eval_order_access4 {
	/*@ requires true;
	  @ ensures true;
	  @*/
	public void caller(Class callme) {
		callme.a = 2 + 2;
	}
}
