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
    // @ public static invariant CardRuntimeException._systemInstance != null;

    //@ public model instance \locset state;
    //@ public model instance \locset reasonRep;
    //@ public accessible \inv : state, reasonRep;
    //@ public accessible state : state, reasonRep;
    //@ public accessible reasonRep : state, reasonRep;
    //@ protected represents reasonRep = _reason[*];
    //@ protected represents state = _reason;


    protected /*@ spec_public non_null @*/ short[] _reason;
    //@ public instance invariant _reason.length == 1;
    //@ public instance invariant JCSystem.isTransient(_reason) == JCSystem.CLEAR_ON_RESET; 

    /*@ public normal_behavior
      @   ensures \fresh(state);
      @   ensures getReason() == reason;
      @   assignable state;
      @*/
    public CardRuntimeException(short reason) {
       this();
	// KeYHelper.setJavaOwner(_reason, this);
       setReason(reason);
    }

    /*@ public normal_behavior
      @   ensures \fresh(state);
      @   assignable state;
      @*/
    CardRuntimeException() {
        _reason = JCSystem.makeTransientShortArray((short) 1,
                JCSystem.CLEAR_ON_RESET);
	// KeYHelper.setJavaOwner(_reason, this);
    }

    /*@ public normal_behavior
      @   accessible state, reasonRep;
      @   ensures \result == getReason();
      @*/
    public /*@ pure @*/ short getReason() {
        return _reason[0];
    }

    /*@ public normal_behavior
      @   assignable reasonRep;
      @   ensures getReason() == reason;
      @*/
    public void setReason(short reason) {
        _reason[0] = reason;
    }

    /*@ public exceptional_behavior
      @   requires CardRuntimeException._systemInstance != null;
      @   requires CardRuntimeException._systemInstance.\inv;
      @   assignable CardRuntimeException._systemInstance.reasonRep;
      @   signals (CardRuntimeException cre) ((CardRuntimeException)cre).getReason() == reason;
      @   signals_only CardRuntimeException;
      @*/
    public static void throwIt(short reason) throws CardRuntimeException {
        CardRuntimeException._systemInstance.setReason(reason);
        throw CardRuntimeException._systemInstance;
    }

}
