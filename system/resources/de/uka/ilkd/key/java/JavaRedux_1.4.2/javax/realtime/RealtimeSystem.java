package javax.realtime;

public class RealtimeSystem{

    //@ public static invariant OOME!=null;

    public static final OutOfMemoryError OOME = new OutOfMemoryError();

    public static OutOfMemoryError oome(){
	return OOME;
    }

}
