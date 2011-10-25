package javacard.framework;

public class TransactionException extends CardRuntimeException {

    private static /*@ spec_public nullable @*/ TransactionException _systemInstance = new TransactionException();
    // @ public static invariant TransactionException._systemInstance != null;

    public final static short IN_PROGRESS = (short) 1;
    // @ public static invariant IN_PROGRESS == 1;
    public final static short NOT_IN_PROGRESS = (short) 2;
    // @ public static invariant NOT_IN_PROGRESS == 2;
    public final static short BUFFER_FULL = (short) 3;
    // @ public static invariant BUFFER_FULL == 3;
    public final static short INTERNAL_FAILURE = (short) 4;
    // @ public static invariant INTERNAL_FAILURE == 4;

    /*@ public exceptional_behavior
      @   requires TransactionException._systemInstance != null;
      @   requires TransactionException._systemInstance.\inv;
      @   assignable TransactionException._systemInstance.reasonRep;
      @   signals (TransactionException te) ((TransactionException)te).getReason() == reason;
      @   signals_only TransactionException;
      @*/
    public static void throwIt(short reason) throws TransactionException {
        TransactionException._systemInstance.setReason(reason);
        throw TransactionException._systemInstance;
    }

}
