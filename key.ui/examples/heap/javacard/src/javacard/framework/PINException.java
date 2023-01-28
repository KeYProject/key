package javacard.framework;

public class PINException extends CardRuntimeException {

    private static /*@ spec_public nullable @*/ PINException _systemInstance = new PINException();
    // @ public static invariant PINException._systemInstance != null;

    public static final short ILLEGAL_VALUE = (short) 1;
    // @ public static invariant ILLEGAL_VALUE == 1;

    /*@ public exceptional_behavior
      @   requires PINException._systemInstance != null;
      @   requires PINException._systemInstance.\inv;
      @   requires \typeof(PINException._systemInstance) == \type(PINException);
      @   assignable PINException._systemInstance.footprint;
      @   signals (PINException pe)
             pe == PINException._systemInstance
          && ((PINException)pe).reason == reason
          && \new_elems_fresh(PINException._systemInstance.footprint);
      @   signals_only PINException;
      @*/
    public static void throwIt(short reason) throws PINException {
        PINException._systemInstance.setReason(reason);
        throw PINException._systemInstance;
    }

}
