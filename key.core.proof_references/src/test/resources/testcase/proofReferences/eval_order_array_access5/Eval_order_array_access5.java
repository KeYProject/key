package eval_order_array_access5;

public class Eval_order_array_access5 {
	/*@requires as.length == 2;
	  @ensures true;
	  @*/
	public void caller(Class callme, int[] as) {
		callme.a = as[0 + 1];
	}
}
