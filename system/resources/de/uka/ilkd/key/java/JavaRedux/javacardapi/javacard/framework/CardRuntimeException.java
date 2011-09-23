/**
  * This file is part of the KeY Java Card API Reference Implementation.
  *
  * Author: Wojciech Mostowski, woj@cs.ru.nl
  *   
  * For details and license see README and LICENSE files.
  *    
  * $Id: CardRuntimeException.java 324 2011-06-16 08:59:15Z woj $
  */

package javacard.framework;

public class CardRuntimeException extends java.lang.RuntimeException {

    private static /*@ spec_public nullable @*/ CardRuntimeException _systemInstance = new CardRuntimeException();
    //@ public invariant CardRuntimeException._systemInstance != null;

    protected /*@ spec_public non_null @*/ short[] _reason;
    //@ public instance invariant _reason.length == 1;
    //@ public instance invariant JCSystem.isTransient(_reason) == JCSystem.CLEAR_ON_RESET; 

    //@ ensures \fresh(_reason);
    //@ ensures getReason() == reason;
    //@ assignable _reason;
    public CardRuntimeException(short reason) {
       this();
	// KeYHelper.setJavaOwner(_reason, this);
       setReason(reason);
    }

    //@ ensures \fresh(_reason);
    //@ assignable _reason;
    CardRuntimeException() {
        _reason = JCSystem.makeTransientShortArray((short) 1,
                JCSystem.CLEAR_ON_RESET);
	// KeYHelper.setJavaOwner(_reason, this);
    }

    //@ ensures \result == _reason[0];
    //@ assignable \nothing;
    public short getReason() {
        return _reason[0];
    }

    //@ ensures getReason() == reason;
    //@ assignable _reason[0];
    public void setReason(short reason) {
        _reason[0] = reason;
    }

    /*@ public exceptional_behavior
      @   requires CardRuntimeException._systemInstance.\inv;
      @   assignable CardRuntimeException._systemInstance._reason[0];
      @   signals (CardRuntimeException cre) ((CardRuntimeException)cre).getReason() == reason;
      @   signals_only CardRuntimeException;
      @*/
    public static void throwIt(short reason) throws CardRuntimeException {
        CardRuntimeException._systemInstance.setReason(reason);
        throw CardRuntimeException._systemInstance;
    }

}
