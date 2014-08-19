package cy;

/**
 *
 * @author christoph
 */
public class MR {
	/*@ normal_behavior
	  @ ensures true;
	  @*/
	public MR() {
	}
	
	public int unspecified() {
		return 42;
	}
	
	/*@ normal_behavior
	  @ ensures \result == 42;
	  @*/
	public int correct() {
		return 42;
	}
	
	/*@ normal_behavior
	  @ ensures \result == 42;
	  @*/
	public int correctUnprovenDependency() {
		return wrong();
	}
	
	/*@ normal_behavior
	  @ ensures \result == 42;
	  @*/
	public int wrong() {
		return 66;
	}

    //@ public normal_behavior ensures false;
    public void a() {
        b();
    }

    //@ public normal_behavior ensures false;
    public void b() {
        a();
    }
}
