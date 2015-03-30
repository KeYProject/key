public class MultipleRecursion {
	/*@ normal_behavior
	  @ ensures false;
	  @*/
    public void a() {
        b();
    }

	/*@ normal_behavior
	  @ ensures false;
	  @*/
    public void b() {
        a();
    }
}