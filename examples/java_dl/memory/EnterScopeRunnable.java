import javax.realtime.*;

public class EnterScopeRunnable implements Runnable{

    ScopedMemory sm;
    Runnable r;

    public EnterScopeRunnable(ScopedMemory sm, Runnable r){
	this.sm = sm;
	this.r = r;
    }

    public void run(){
	sm.enter(r);
    }
}
