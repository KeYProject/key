package javax.realtime;

public class RealtimeSystem{

    //@ public static invariant \inImmortalMemory(OOME);

    // public static invariant IAE!=null && \inImmortalMemory(IAE);

    //@ public static invariant \inImmortalMemory(TBE);

    //@ public static invariant \inImmortalMemory(TRASH);

    public static final OutOfMemoryError OOME = new OutOfMemoryError();

    public static final ScopedMemory TRASH = new LTMemory(0);

    //    public static final IllegalAssignmentError IAE = 
    //	new IllegalAssignmentError();

    public static final ThrowBoundaryError TBE = 
	new ThrowBoundaryError();

    public static OutOfMemoryError oome(){
	return OOME;
    }

    //    public static IllegalAssignmentError iae(){
    //	return IAE;
    //    }

    public static ThrowBoundaryError tbe(){
	return TBE;
    }

}
