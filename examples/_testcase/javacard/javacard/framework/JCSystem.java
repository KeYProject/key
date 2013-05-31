// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 

package javacard.framework;

import de.uka.ilkd.key.javacard.*;

/** Some of the methods in this class do not have any spec. This
  * is because it is better to execute them symbolically (inline the
  * implementation) in a KeY proof and let dedicated taclets for jvm*
  * methods take care of the rest. Such no spec methods are marked
  * with "no spec"
  */
public final class JCSystem {

    public static final byte NOT_A_TRANSIENT_OBJECT = (byte)0;
    public static final byte CLEAR_ON_RESET = (byte)1;
    public static final byte CLEAR_ON_DESELECT = (byte)2;

    public static final byte MEMORY_TYPE_PERSISTENT = (byte)0;
    public static final byte MEMORY_TYPE_TRANSIENT_RESET = (byte)1;
    public static final byte MEMORY_TYPE_TRANSIENT_DESELECT = (byte)2;

    private static final short API_VERSION = (short)0x0202;

    /*@ static invariant _transactionDepth >= 0; @*/
    private /*@ spec_public @*/ static byte _transactionDepth;

    // no spec
    public static byte isTransient(Object theObj){
        if(theObj == null) return NOT_A_TRANSIENT_OBJECT;
	return KeYJCSystem.jvmIsTransient(theObj);
    }

    // no spec
    public static boolean[] makeTransientBooleanArray(short length, byte event)
      throws SystemException {
          if(event != CLEAR_ON_RESET && event != CLEAR_ON_DESELECT)
	    SystemException.throwIt(SystemException.ILLEGAL_VALUE);
  	  return KeYJCSystem.
	    jvmMakeTransientBooleanArray(length, event);
	}

    // no spec
    public static byte[] makeTransientByteArray(short length, byte event)
      throws SystemException {
          if(event != CLEAR_ON_RESET && event != CLEAR_ON_DESELECT)
	    SystemException.throwIt(SystemException.ILLEGAL_VALUE);
	return KeYJCSystem.
	  jvmMakeTransientByteArray(length, event);
    }

    // no spec
    public static short[] makeTransientShortArray(short length, byte event)
      throws SystemException {
        if(event != CLEAR_ON_RESET && event != CLEAR_ON_DESELECT)
          SystemException.throwIt(SystemException.ILLEGAL_VALUE);
	return KeYJCSystem.
	  jvmMakeTransientShortArray(length, event);
    }

    // no spec
    public static Object[] makeTransientObjectArray(short length, byte event) 
       throws SystemException {
        if(event != CLEAR_ON_RESET && event != CLEAR_ON_DESELECT)
          SystemException.throwIt(SystemException.ILLEGAL_VALUE);
	return KeYJCSystem.
	  jvmMakeTransientObjectArray(length, event);
     }

     /*@ normal_behavior
          requires true;
	  ensures \result == API_VERSION;
  	assignable \nothing;
       @*/
     public static short getVersion() {
       return API_VERSION;
     }

    // no spec
    public static void beginTransaction() throws TransactionException {
	if(_transactionDepth != 0)
	   TransactionException.throwIt(TransactionException.IN_PROGRESS);
        _transactionDepth++;
	KeYJCSystem.jvmBeginTransaction();
    }
 
    // no spec
    public static void abortTransaction() throws TransactionException {
	if(_transactionDepth == 0)
	    TransactionException.throwIt(TransactionException.NOT_IN_PROGRESS);
	KeYJCSystem.jvmAbortTransaction();
	_transactionDepth--;
    }

    // no spec
    public static void commitTransaction() throws TransactionException {
	if(_transactionDepth == 0)
	    TransactionException.throwIt(TransactionException.NOT_IN_PROGRESS);
	KeYJCSystem.jvmCommitTransaction();
	_transactionDepth--;
    }

    /*@ normal_behavior
        requires true;
	ensures \result == _transactionDepth;
	assignable \nothing;
     @*/
    public static byte getTransactionDepth() {
	return _transactionDepth;
    }

} 
