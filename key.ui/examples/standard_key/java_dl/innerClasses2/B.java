
public class B extends A{

    public int i=1;

    /*@ public normal_behavior
      @  ensures \result==true;
      @*/
    public boolean test(){
	A a = new B();
	A.InnerA ia = a.new InnerA();
	InnerB ib = new InnerB(a);
	return ia.m()==ib.m() && ia.m()==0 && ib.n()==i;
    }

    class InnerB extends A.InnerA{
	
	public InnerB(A a){
	    a.super();
	}

	/*@ public normal_behavior
	  @  ensures \result==B.this.i;
	  @*/
	public int n(){
	    return i;
	}

    }

}
