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

public class TransactionException extends CardRuntimeException  {

   /*@ static invariant \is_initialized(TransactionException); @*/
   /*@ static invariant _systemInstance != null; @*/
   private static TransactionException _systemInstance;

   public final static short IN_PROGRESS = (short)1;
   public final static short NOT_IN_PROGRESS = (short)2;
   public final static short BUFFER_FULL = (short)3;
   public final static short INTERNAL_FAILURE = (short)4;   

   /*@ exceptional_behavior
        requires true;
	signals (TransactionException te) te == _systemInstance && te._reason[0] == reason ;
	assignable _systemInstance._reason[0] ;
   @*/
   public static void throwIt(short reason) throws TransactionException {
      _systemInstance.setReason(reason);
      throw _systemInstance;
   }

} 
