package javacard.framework;

public class PINException extends CardRuntimeException {

    private static /*@ spec_public nullable @*/ PINException _systemInstance = new PINException();
    // @ public static invariant PINException._systemInstance != null;

    public static final short ILLEGAL_VALUE = (short) 1;
    // @ public static invariant ILLEGAL_VALUE == 1;

    /*@ public exceptional_behavior
      @   requires PINException._systemInstance != null;
      @   requires PINException._systemInstance.\inv;
      @   assignable PINException._systemInstance.reasonRep;
      @   signals (PINException pe) ((PINException)pe).getReason() == reason;
      @   signals_only PINException;
      @*/
    public static void throwIt(short reason) throws PINException {
        _systemInstance.setReason(reason);
        throw _systemInstance;
    }

}
