package javax.realtime;

public class RealtimeSystem{

    //@ public static invariant OOME!=null && \inImmortalMemory(OOME);

    //@ public static invariant IAE!=null && \inImmortalMemory(IAE);

    //@ public static invariant TBE!=null && \inImmortalMemory(TBE);

    public static final OutOfMemoryError OOME = new OutOfMemoryError();

    public static final IllegalAssignmentError IAE = 
	new IllegalAssignmentError();

    public static final ThrowBoundaryError TBE = 
	new ThrowBoundaryError();

    public static OutOfMemoryError oome(){
	return OOME;
    }

    public static IllegalAssignmentError iae(){
	return IAE;
    }

    public static IllegalAssignmentError tbe(){
	return TBE;
    }

}
