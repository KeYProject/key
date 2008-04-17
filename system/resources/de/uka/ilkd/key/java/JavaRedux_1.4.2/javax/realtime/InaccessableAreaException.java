package javax.realtime;

public class InaccessableAreaException extends RuntimeException{

    public InaccessableAreaException(){ super();}

    public InaccessableAreaException(String s){
	super(s);
    }

}
