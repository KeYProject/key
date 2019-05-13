
public class PredicateEvaluationComposedTerms {

	//@ invariant a >= 0 || b >= 0;
	public int a;
	public int b;
	
	/*@ normal_behavior
	  @ ensures \result == 42;
	  @ assignable a, b;
	  @*/
	public int main() {
		a = -1;
		b = 1;
		return 42;
	}
}
