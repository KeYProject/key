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
public class Util  { 

    // In principle this method could have a spec, but it would be
    // very elaborate and very difficult for the src == dest case, so:
    //
    // no spec
    public static short arrayCopy(byte[] src, short  srcOff,
                                  byte[] dest, short  destOff, short  length) throws TransactionException {
	if(src == null || dest == null) throw new NullPointerException();
	if(length < 0 ||
	   srcOff < 0 || destOff < 0 ||
	   (short)(srcOff + length) > src.length || 
	   (short)(destOff + length) > dest.length)
	  throw new ArrayIndexOutOfBoundsException();
        // arrayCopy is supposed to be atomic if the destination is
	// persistent, start a transaction, unless there is one
	// already
	final boolean doTransaction =
	  JCSystem.isTransient(dest) == JCSystem.NOT_A_TRANSIENT_OBJECT
	     && JCSystem.getTransactionDepth() == (byte)0;
	if(doTransaction) KeYJCSystem.jvmBeginTransaction();
        // From now on we use jvmArrayCopy, which should be "well formed", i.e.
	// it will not throw any exception. In a KeY proof
	// it will be treated by a dedicated taclet.
	if(src == dest) {
 	  byte[] _tempArray = new byte[length];
	  KeYJCSystem.jvmArrayCopy(src, srcOff, _tempArray, (short)0, length);
	  KeYJCSystem.jvmArrayCopy(_tempArray, (short)0, dest, destOff, length);
        }else{
	  KeYJCSystem.jvmArrayCopy(src, srcOff, dest, destOff, length);
	}
	if(doTransaction) KeYJCSystem.jvmCommitTransaction();
	return (short)(destOff+length);
    }

    // Same as above: no spec
    public static short arrayCopyNonAtomic(byte[] src, short  srcOff,
                                              	 byte[] dest, short  destOff,
                                              	 short  length){

	if(src == null || dest == null) throw new NullPointerException();
	if(length < 0 ||
	   srcOff < 0 || destOff < 0 ||
	   srcOff + length > src.length || destOff + length > dest.length)
	  throw new ArrayIndexOutOfBoundsException();
        // From now on we use jvmArrayCopy and jvmArrayCopyNonAtomic,
	// which should be "well formed", i.e. they will not throw any exception.
	// In a KeY proof they will be treated by dedicated taclets.
        if(src == dest) {
	  byte[] _tempArray = new byte[length];
	  KeYJCSystem.jvmArrayCopy(src, srcOff, _tempArray, (short)0, length);
	  KeYJCSystem.jvmArrayCopyNonAtomic(_tempArray, (short)0, dest, destOff, length);
	}else{
	  KeYJCSystem.jvmArrayCopyNonAtomic(src, srcOff, dest, destOff, length);
	}
	return (short)(destOff+length);
    }

    // Same as above: no spec
    public static short arrayFillNonAtomic(byte[] bArray, short  bOff,
                                              	 short  bLen, byte   bValue) {
	if(bArray == null) throw new NullPointerException();
	if(bLen < 0 || bOff < 0 || (short)(bOff + bLen) > bArray.length)
	  throw new ArrayIndexOutOfBoundsException();
        // From now on we use jvmArrayFillNonAtomic, which should be
	// "well formed", i.e. it will not throw any exception.
	// In a KeY proof it will be treated by a dedicated taclet.
        KeYJCSystem.jvmArrayFillNonAtomic(bArray, bOff, bLen, bValue);
	return (short)(bOff+bLen);
    }

    /*@ normal_behavior
          requires src != null;
	  requires dest != null;
	  requires srcOff >= 0 ;
	  requires destOff >= 0 ;
	  requires length >=0;
	  requires (short)(srcOff + length) <= src.length;
	  requires (short)(destOff + length) <= dest.length;
          ensures  \result == 0 || \result == 1 || \result == -1;
	  assignable \nothing;
    @*/
    public static byte arrayCompare(byte[] src, short  srcOff,
                                    byte[] dest, short  destOff,
                                    short  length) {
	if(src == null || dest == null) throw new NullPointerException();
	if(length < 0 ||
	   srcOff < 0 || destOff < 0 ||
	   (short)(srcOff + length) > src.length || 
	   (short)(destOff + length) > dest.length)
	  throw new ArrayIndexOutOfBoundsException();
	return KeYJCSystem.jvmArrayCompare(src, srcOff, dest, destOff, length);
    }

    // no spec
    public static short makeShort(byte b1, byte b2) {
        return KeYJCSystem.jvmMakeShort(b1, b2);
    }
 
    // Could be specified, but KeY does not handle byte and short
    // args. in query methods very well, see bug #638
    //
    // no spec
    public static short getShort(byte[] bArray, short bOff) {
	if(bArray == null) throw new NullPointerException();
	if(bOff < 0 || (short)(bOff + 1) >= bArray.length)
	  throw new ArrayIndexOutOfBoundsException();
	return KeYJCSystem.jvmMakeShort(
	  bArray[bOff], bArray[bOff+1]);
    }

    // no spec
    public static short setShort(byte[] bArray, short  bOff, short  sValue) 
      throws TransactionException {
	if(bArray == null) throw new NullPointerException();
	if(bOff < 0 || (short)(bOff + 1) >= bArray.length)
	  throw new ArrayIndexOutOfBoundsException();
	final boolean doTransaction = JCSystem.isTransient(bArray) == JCSystem.NOT_A_TRANSIENT_OBJECT
	                        && JCSystem.getTransactionDepth() == (byte)0;
	if(doTransaction) KeYJCSystem.jvmBeginTransaction();
        KeYJCSystem.jvmSetShort(bArray, bOff, sValue);
	if(doTransaction) KeYJCSystem.jvmCommitTransaction();
        return (short)(bOff + 2);
    }

}
