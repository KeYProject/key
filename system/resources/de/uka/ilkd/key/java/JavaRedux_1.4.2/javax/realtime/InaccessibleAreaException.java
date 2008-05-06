package javax.realtime;

public class InaccessibleAreaException extends RuntimeException{

    public InaccessibleAreaException(){ super();}

    public InaccessibleAreaException(String s){
	super(s);
    }

}
