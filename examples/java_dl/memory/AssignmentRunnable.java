public class AssignmentRunnable implements Runnable{
    
    RefCont r;

    public AssignmentRunnable(RefCont r){
	this.r = r;
    }

    public void run(){
	RefCont t = new RefCont();
	t.ref = r;
	
    }

}
