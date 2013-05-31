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

public class CardRuntimeException extends java.lang.RuntimeException {

   /*@ static invariant \is_initialized(CardRuntimeException) ; @*/
   /*@ static invariant _systemInstance != null; @*/
   private static CardRuntimeException _systemInstance;

   /*@ invariant _reason != null && _reason.length == 1; @*/
   /*@ invariant JCSystem.isTransient(_reason) == JCSystem.CLEAR_ON_RESET ; @*/
   protected /*@ spec_public @*/ short[] _reason;

   /*@ normal_behavior
        requires true;
	ensures  \old(_systemInstance) == null ==> _systemInstance == this;
	assignable _reason, _reason[0], _systemInstance;
   @*/
   public CardRuntimeException() {
      _reason = JCSystem.makeTransientShortArray((short)1,JCSystem.CLEAR_ON_RESET);
      if (_systemInstance==null)
	 _systemInstance = this;
   }

   /*@ normal_behavior
        requires true;
	ensures _reason[0] == reason;
	ensures \old(_systemInstance) == null ==> _systemInstance == this;
	assignable _reason, _reason[0], _systemInstance;
   @*/
   public CardRuntimeException(short reason) {
      _reason = JCSystem.makeTransientShortArray((short)1,JCSystem.CLEAR_ON_RESET);
      _reason[0] = reason;
      if (_systemInstance==null)
         _systemInstance = this;
   }

   /*@ normal_behavior
        requires true;
	ensures \result == _reason[0];
	assignable \nothing; 
   @*/
   public short getReason() {
      return _reason[0];
   }

   /*@ normal_behavior
        requires true;
	ensures _reason[0] == reason ;
	assignable _reason[0] ;
   @*/
   public void setReason(short reason) {
      _reason[0] = reason;
   }

   /*@ exceptional_behavior
        requires true;
	signals (CardRuntimeException cre) cre == _systemInstance && cre._reason[0] == reason ;
	assignable _systemInstance._reason[0] ;
   @*/
   public static void throwIt(short reason) throws CardRuntimeException {
      _systemInstance.setReason(reason);
      throw _systemInstance;
   }

} 
