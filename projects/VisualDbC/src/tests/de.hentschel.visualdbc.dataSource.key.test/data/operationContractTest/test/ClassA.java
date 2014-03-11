public class ClassA {
	private int x = 5;
	
	/*@
    @ public normal_behavior
    @ requires true;
    @ ensures x == 5;
    @ assignable \nothing;
    @*/		
	public ClassA() {
	}
	
	/*@
    @ public normal_behavior
    @ requires true;
    @ ensures this.x == x;
    @ assignable \nothing;
    @*/		
	public ClassA(int x) {
		this.x = x;
	}

    /*@
    @ public normal_behavior
    @ requires true;
    @ ensures \result == x;
    @ assignable \nothing;
    @*/	
	public int getX() {
		return x;
	}

    /*@
    @ public normal_behavior
    @ requires true;
    @ ensures this.x == x;
    @ assignable \nothing;
    @*/		
	public void setX(int x) {
		this.x = x;
	}
}