public class TestRunnable implements Runnable{

    Test t;
    boolean ios;

    public TestRunnable(Test t, boolean executeInOuterScope){
	this.t = t;
	this.ios = executeInOuterScope;
    }

    public void run(){
	Test nt = new Test();
	if(ios){
	    t.next = nt;
	}else{
	    nt.next = t;
	} 
    }
}
