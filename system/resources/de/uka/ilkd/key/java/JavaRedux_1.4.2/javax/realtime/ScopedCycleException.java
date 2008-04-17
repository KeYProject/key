package javax.realtime;

public class ScopedCycleException extends RuntimeException{

    public ScopedCycleException(){ super();}

    public ScopedCycleException(String s){
	super(s);
    }

}
