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

public class SystemException extends CardRuntimeException { 

   /*@ static invariant \is_initialized(SystemException); @*/
   /*@ static invariant _systemInstance != null; @*/
   private /*@ spec_public @*/ static SystemException _systemInstance;
  
   public static final short ILLEGAL_VALUE = (short)1;
   public static final short NO_TRANSIENT_SPACE = (short)2;
   public static final short ILLEGAL_TRANSIENT = (short)3;
   public static final short ILLEGAL_AID = (short)4;
   public static final short NO_RESOURCE = (short)5;
   public static final short ILLEGAL_USE = (short)6;

   /*@ exceptional_behavior
        requires true;
	signals (SystemException se) se == _systemInstance && se._reason[0] == reason ;
	assignable _systemInstance._reason[0] ;
   @*/
  public static void throwIt(short reason) throws SystemException {
     _systemInstance.setReason(reason);
     throw _systemInstance;  
} 
}
