package test;

public class AccessibleTest {
	private int x;
	
	public AccessibleTest(int x) {
		this.x = x;
	}
}

class B {
    //@ accessible \inv : this.*, c.*;
    public final /*@ nullable @*/ AccessibleTest c;
    
    //@ invariant \invariant_for(c);
    
    B(int x) { c = new AccessibleTest(x); }
}