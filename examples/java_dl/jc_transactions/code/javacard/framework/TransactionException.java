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
