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

package de.uka.ilkd.key.javacard;

/** This class contains methods specific to KeY model of the Java Card
  * API (2.1.1 & 2.2.1). These methods do not have any specs as they
  * should be always symbolically exected in the proof with dedicated
  * taclets. No contracts should be used for these methods (especially
  * the jvm*Transaction methods).
  */
public class KeYJCSystem {

    public static native byte jvmIsTransient(Object theObj);

    public static native boolean[] jvmMakeTransientBooleanArray(
      short length, byte event) ;

    public static native byte[] jvmMakeTransientByteArray(
      short length, byte event) ;

    public static native short[] jvmMakeTransientShortArray(
      short length, byte event) ;

    public static native Object[] jvmMakeTransientObjectArray(
      short length, byte event) ;
    
    public final static native void jvmBeginTransaction();

    public static native void jvmAbortTransaction();

    public static native void jvmCommitTransaction();

    public static native void jvmSuspendTransaction();

    public static native void jvmResumeTransaction();

    public static native void jvmArrayCopy(
      byte[] src, short srcOff, byte[] dest, short destOff, short  length);
    
    public static native void jvmArrayCopyNonAtomic(
      byte[] src, short srcOff, byte[] dest, short destOff, short  length);

    public static native void jvmArrayFillNonAtomic(
      byte[] bArray, short bOff, short bLen, byte  bValue);

    public static native byte jvmArrayCompare(
      byte[] src, short srcOff, byte[] dest, short destOff, short  length);

    public static native short jvmMakeShort(byte b1, byte b2);

    public static native short jvmSetShort(
      byte[] bArray, short  bOff, short  sValue);

}
