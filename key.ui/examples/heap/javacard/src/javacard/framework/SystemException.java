package javacard.framework;

public class SystemException extends CardRuntimeException {

    private static /*@ spec_public nullable @*/ SystemException _systemInstance = new SystemException();
    // @ public invariant SystemException._systemInstance != null;

    public static final short ILLEGAL_VALUE = (short) 1;
    // @ public static invariant ILLEGAL_VALUE == 1;
    public static final short NO_TRANSIENT_SPACE = (short) 2;
    // @ public static invariant NO_TRANSIENT_SPACE == 2;
    public static final short ILLEGAL_TRANSIENT = (short) 3;
    // @ public static invariant ILLEGAL_TRANSIENT == 3;
    public static final short ILLEGAL_AID = (short) 4;
    // @ public static invariant ILLEGAL_AID == 4;
    public static final short NO_RESOURCE = (short) 5;
    // @ public static invariant NO_RESOURCE == 5;
    public static final short ILLEGAL_USE = (short) 6;
    // @ public static invariant ILLEGAL_USE == 6;

    /*@ public exceptional_behavior
      @   requires SystemException._systemInstance != null;
      @   requires SystemException._systemInstance.\inv;
      @   requires \typeof(SystemException._systemInstance) == \type(SystemException);
      @   assignable SystemException._systemInstance.footprint;
      @   signals (SystemException se)
             se == SystemException._systemInstance
          && ((SystemException)se).reason == reason
          && \new_elems_fresh(SystemException._systemInstance.footprint);
      @   signals_only SystemException;
      @*/
    public static void throwIt(short reason) throws SystemException {
        SystemException._systemInstance.setReason(reason);
        throw SystemException._systemInstance;
    }
}
