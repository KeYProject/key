package javax.realtime;

public class InaccessibleAreaException extends RuntimeException{

    public InaccessibleAreaException(){ super();}

    public InaccessibleAreaException(String arg0){
	super(arg0);
    }

}
