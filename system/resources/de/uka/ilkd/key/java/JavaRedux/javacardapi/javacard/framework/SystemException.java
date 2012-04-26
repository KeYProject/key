/**
  * This file is part of the KeY Java Card API Reference Implementation.
  *
  * Author: Wojciech Mostowski, woj@cs.ru.nl
  *   
  * For details and license see README and LICENSE files.
  *    
  * $Id: SystemException.java 324 2011-06-16 08:59:15Z woj $
  */

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
      @   assignable SystemException._systemInstance.reasonRep;
      @   signals (SystemException se) ((SystemException)se).getReason() == reason;
      @   signals_only SystemException;
      @*/
    public static void throwIt(short reason) throws SystemException {
        SystemException._systemInstance.setReason(reason);
        throw SystemException._systemInstance;
    }
}
