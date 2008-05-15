public class A{

    public int i=0;

    class InnerA{
	
	/*@ public normal_behavior
	  @  ensures \result==A.this.i;
	  @*/
	public int m(){
	    return i;
	}

    }

}
