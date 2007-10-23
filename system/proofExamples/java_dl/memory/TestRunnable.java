public class TestRunnable implements Runnable{

    Test t;

    public TestRunnable(Test t){
	this.t = t;
    }

    public void run(){
	Test nt = new Test();
	nt.next = t; 
    }
}
