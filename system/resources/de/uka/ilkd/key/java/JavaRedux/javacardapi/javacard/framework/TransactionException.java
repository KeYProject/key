/**
  * This file is part of the KeY Java Card API Reference Implementation.
  *
  * Author: Wojciech Mostowski, woj@cs.ru.nl
  *   
  * For details and license see README and LICENSE files.
  *    
  * $Id: TransactionException.java 324 2011-06-16 08:59:15Z woj $
  */

package javacard.framework;

public class TransactionException extends CardRuntimeException {

    private static /*@ spec_public nullable @*/ TransactionException _systemInstance = new TransactionException();
    // @ public invariant TransactionException._systemInstance != null;

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
