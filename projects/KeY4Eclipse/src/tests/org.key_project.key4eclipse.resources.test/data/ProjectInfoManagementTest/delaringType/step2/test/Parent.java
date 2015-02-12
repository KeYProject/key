
public class Parent {
	protected int x;
	
	/*@ normal_behavior
	  @ ensures true;
	  @*/
	public Parent() {
	}
	
	/*@ normal_behavior
	  @ ensures \result == 42;
	  @*/
	public int magic() {
		return 42;
	}
	
	//@ model int ofm;
	//@ represents ofm = 2*x;
    //@ accessible ofm : this.x;
	
	public class ParentInner {
		protected int innerX;
		
		/*@ normal_behavior
		  @ ensures \result == 42;
		  @*/
		public int innerMagic() {
			return 42;
		}
	}
}
