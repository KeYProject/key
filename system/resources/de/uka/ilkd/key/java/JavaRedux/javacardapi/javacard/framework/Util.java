package javacard.framework;

public class Util {

    /*@
         public transaction behavior
           requires JCSystem.npe != null;
           requires JCSystem.aioobe != null;
           requires JCSystem.isTransient(dest) != JCSystem.NOT_A_TRANSIENT_OBJECT ==> !\transactionUpdated(dest);
           requires src.length < 32768;
           requires dest.length < 32768;
           ensures \result == destOffset + length;
           ensures (\forall short i; i>=0 && i<length; dest[destOffset + i] == \old(src[srcOffset + i]));
           ensures (\forall short i; i>=0 && i<length; \backup(dest[destOffset + i]) == 
                 ((JCSystem.isTransient(dest) == JCSystem.NOT_A_TRANSIENT_OBJECT && \backup(\transactionUpdated(dest))) ?  
                    \old(\backup(dest[destOffset + i]))
                  : \old(src[srcOffset + i]))
              );
           signals (NullPointerException npe) npe == JCSystem.npe && (src == null || dest == null);
           signals (ArrayIndexOutOfBoundsException aioobe) aioobe == JCSystem.aioobe && (length < 0 ||
               srcOffset < 0 || destOffset < 0 ||
               srcOffset + length > src.length || destOffset + length > dest.length);
           signals_only NullPointerException, ArrayIndexOutOfBoundsException;
           assignable dest[destOffset..destOffset+length-1];
           assignable_backup dest[destOffset..destOffset+length-1];

         also

         public behavior
           requires JCSystem.npe != null;
           requires JCSystem.aioobe != null;
           requires src.length < 32768;
           requires dest.length < 32768;
           ensures \result == destOffset + length;
           ensures (\forall short i; i>=0 && i<length; dest[destOffset + i] == \old(src[srcOffset + i]));
           signals (NullPointerException npe) npe == JCSystem.npe && (src == null || dest == null);
           signals (ArrayIndexOutOfBoundsException aioobe) aioobe == JCSystem.aioobe && (length < 0 ||
               srcOffset < 0 || destOffset < 0 ||
               srcOffset + length > src.length || destOffset + length > dest.length);
           signals_only NullPointerException, ArrayIndexOutOfBoundsException;
           assignable dest[destOffset..destOffset+length-1];

      @*/
    public static final short arrayCopyNonAtomic(/*@ nullable @*/ byte[] src, short srcOffset,
            /*@ nullable @*/ byte[] dest, short destOffset, short length)
            throws NullPointerException, ArrayIndexOutOfBoundsException {

        if (src == null || dest == null)
            throw JCSystem.npe;
        if (length < 0 || srcOffset < 0 || destOffset < 0
                || srcOffset  > (short)(src.length - length)
                || destOffset > (short)(dest.length - length))
            throw JCSystem.aioobe;

        if(src == dest && srcOffset == destOffset) {
          return (short) (destOffset + length);
        }
        final boolean changeTransient =
          (JCSystem.nativeKeYGetTransient(dest) == JCSystem.NOT_A_TRANSIENT_OBJECT);
        if(changeTransient) {
          JCSystem.nativeKeYSetTransient(dest, JCSystem.CLEAR_ON_RESET);
        }
        if(src != dest || srcOffset > destOffset) {
          /*@
             loop_invariant i >= 0 && i <= length &&
                srcOffset + i >= 0 && srcOffset + i <= src.length &&
                destOffset + i >= 0 && destOffset + i <= dest.length &&
               (\forall short j; j >= 0 && j< length;
                   dest[destOffset + j] == (j<i ? \old(src[srcOffset + j]) : \old(dest[destOffset + j]))
               )
             ;
             loop_invariant_transaction
               (\forall short j; j >= 0 && j < length; 
                  \backup(dest[destOffset + j]) ==
                    ((j >= i || \backup(\transactionUpdated(dest))) ?
                        \old(\backup(dest[destOffset + j])) :
                        \old(src[srcOffset + j]))
               );
             decreases length - i;
             assignable dest[destOffset..destOffset+length-1];
             assignable_backup dest[destOffset..destOffset+length-1];
          @*/
          for(short i=0;i<length;i++) {
              dest[destOffset + i] = src[srcOffset + i];
          }
        }else{
          /*@
             loop_invariant i >= 0 && i <= length &&
                srcOffset + length - i >= 0 && srcOffset + length - i  <= src.length &&
                destOffset + length - i >= 0 && destOffset + length - i <= dest.length
                &&
                (\forall short j; j >= 0 && j < length; 
                    dest[destOffset + j] == (j >= length - i ? \old(src[srcOffset + j]) : \old(dest[destOffset + j]))
                )
             ;
             loop_invariant_transaction
               (\forall short j; j >= 0 && j < length; 
                  \backup(dest[destOffset + j]) ==
                    ((j < length - i || \backup(\transactionUpdated(dest))) ?
                        \old(\backup(dest[destOffset + j])) :
                        \old(src[srcOffset + j]))
               );
             decreases length - i;
             assignable dest[destOffset..destOffset+length-1];
             assignable_backup dest[destOffset..destOffset+length-1];
          @*/
          for(short i=0; i<length; i++) {
            dest[destOffset + (length - 1) - i] = src[srcOffset + (length - 1) - i];
          }
        }
        if(changeTransient) {      
          JCSystem.nativeKeYSetTransient(dest, JCSystem.NOT_A_TRANSIENT_OBJECT);
        }
        return (short) (destOffset + length);
    }


    /*@
         public transaction behavior
           requires JCSystem.npe != null;
           requires JCSystem.aioobe != null;
           requires JCSystem.getTransactionDepth() == 1;
           requires src.length < 32768;
           requires dest.length < 32768;
           requires JCSystem.isTransient(dest) != JCSystem.NOT_A_TRANSIENT_OBJECT ==> !\transactionUpdated(dest);
           ensures \result == destOffset + length;
           ensures (\forall short i; i>=0 && i<length; dest[destOffset + i] == \old(src[srcOffset + i]));
           ensures (JCSystem.isTransient(dest) == JCSystem.NOT_A_TRANSIENT_OBJECT && length > 0)
                ==> \backup(\transactionUpdated(dest));
           ensures  JCSystem.isTransient(dest) != JCSystem.NOT_A_TRANSIENT_OBJECT ==>
                !\backup(\transactionUpdated(dest));
           ensures (\forall short i; i>=0 && i<length; \backup(dest[destOffset + i]) == 
                 (JCSystem.isTransient(dest) == JCSystem.NOT_A_TRANSIENT_OBJECT ?  
                    \old(\backup(dest[destOffset + i]))
                  : \old(src[srcOffset + i]))
              );
           signals (NullPointerException npe) npe == JCSystem.npe && (src == null || dest == null);
           signals (ArrayIndexOutOfBoundsException aioobe) aioobe == JCSystem.aioobe && (length < 0 ||
               srcOffset < 0 || destOffset < 0 ||
               srcOffset + length > src.length || destOffset + length > dest.length);
           signals_only NullPointerException, ArrayIndexOutOfBoundsException;
           assignable dest[destOffset..destOffset+length-1];
           assignable_backup \transactionUpdated(dest), dest[destOffset..destOffset+length-1];

         also

         public behavior
           requires JCSystem.getTransactionDepth() == 0;
           requires JCSystem.npe != null;
           requires JCSystem.aioobe != null;
           requires src.length < 32768;
           requires dest.length < 32768;
           requires JCSystem.isTransient(dest) != JCSystem.NOT_A_TRANSIENT_OBJECT ==> !\transactionUpdated(dest);
           ensures \result == destOffset + length;
           ensures (\forall short i; i>=0 && i<length; dest[destOffset + i] == \old(src[srcOffset + i]));
           signals (NullPointerException npe) npe == JCSystem.npe && (src == null || dest == null);
           signals (ArrayIndexOutOfBoundsException aioobe) aioobe == JCSystem.aioobe && (length < 0 ||
               srcOffset < 0 || destOffset < 0 ||
               srcOffset + length > src.length || destOffset + length > dest.length);
           signals_only NullPointerException, ArrayIndexOutOfBoundsException;
           assignable dest[destOffset..destOffset+length-1];

      @*/
    public static final short arrayCopy(/*@ nullable @*/ byte[] src, short srcOffset,
            /*@ nullable @*/ byte[] dest, short destOffset, short length)
            throws NullPointerException, ArrayIndexOutOfBoundsException {

        if (src == null || dest == null)
            throw JCSystem.npe;
        if (length < 0 || srcOffset < 0 || destOffset < 0
                || srcOffset  > (short)(src.length - length)
                || destOffset > (short)(dest.length - length))
            throw JCSystem.aioobe;

        if(src == dest && srcOffset == destOffset) {
          return (short) (destOffset + length);
        }
        final boolean startTransaction = (JCSystem.getTransactionDepth() == 0);
        if(startTransaction) {
          JCSystem.beginTransaction();
        }
        if(src != dest || srcOffset > destOffset) {
          /*@
             loop_invariant i >= 0 && i <= length &&
                srcOffset + i >= 0 && srcOffset + i <= src.length &&
                destOffset + i >= 0 && destOffset + i <= dest.length &&
               (\forall short j; j >= 0 && j< length;
                   dest[destOffset + j] == (j<i ? \old(src[srcOffset + j]) : \old(dest[destOffset + j]))
               )
             ;
             loop_invariant_transaction true 
                &&
               (JCSystem.isTransient(dest) == JCSystem.NOT_A_TRANSIENT_OBJECT && i != 0  ==> \backup(\transactionUpdated(dest))) 
                &&
               (JCSystem.isTransient(dest) != JCSystem.NOT_A_TRANSIENT_OBJECT ==> !\backup(\transactionUpdated(dest))) 
                &&
               (\forall short j; j >= 0 && j < length; 
                  \backup(dest[destOffset + j]) ==
                    ((j >= i || JCSystem.isTransient(dest) == JCSystem.NOT_A_TRANSIENT_OBJECT) ?
                        \old(\backup(dest[destOffset + j])) :
                        \old(src[srcOffset + j]))
               )
             ;
             decreases length - i;
             assignable dest[destOffset..destOffset+length-1];
             assignable_backup \transactionUpdated(dest), dest[destOffset..destOffset+length-1];
          @*/
          for(short i=0;i<length;i++) {
              dest[destOffset + i] = src[srcOffset + i];
          }
        }else{
          /*@
             loop_invariant i >= 0 && i <= length &&
                srcOffset + length - i >= 0 && srcOffset + length - i  <= src.length &&
                destOffset + length - i >= 0 && destOffset + length - i <= dest.length &&
                (\forall short j; j >= 0 && j < length; 
                    dest[destOffset + j] == (j >= length - i ? \old(src[srcOffset + j]) : \old(dest[destOffset + j]))
                )
             ;
             loop_invariant_transaction
                (JCSystem.isTransient(dest) == JCSystem.NOT_A_TRANSIENT_OBJECT && i != 0  ==> \backup(\transactionUpdated(dest))) &&
               (JCSystem.isTransient(dest) != JCSystem.NOT_A_TRANSIENT_OBJECT ==> !\backup(\transactionUpdated(dest))) 
                &&
               (\forall short j; j >= 0 && j < length; 
                  \backup(dest[destOffset + j]) ==
                    ((j < length - i || JCSystem.isTransient(dest) == JCSystem.NOT_A_TRANSIENT_OBJECT) ?
                        \old(\backup(dest[destOffset + j])) :
                        \old(src[srcOffset + j]))
               );
             decreases length - i;
             assignable dest[destOffset..destOffset+length-1];
             assignable_backup \transactionUpdated(dest), dest[destOffset..destOffset+length-1];
          @*/
          for(short i=0; i<length; i++) {
            dest[destOffset + (length - 1) - i] = src[srcOffset + (length - 1) - i];
          }
        }
        if(startTransaction) {
          JCSystem.commitTransaction();
        }
        return (short) (destOffset + length);
    }

    /*@
         public normal_behavior
           requires src.length < 32768;
           requires dest.length < 32768;
           requires src != null && dest != null;
           requires length >= 0;
           requires srcOffset >=0 & srcOffset + length <= src.length;
           requires destOffset >=0 & destOffset + length <= dest.length;
           ensures \result == -1 || \result == 0 || \result == 1;
           ensures \result == 0 ==> (\forall short i; i>=0 && i < length; src[srcOffset + i] == dest[destOffset + i]);
           ensures \result == -1 ==>
              (\exists short i; i>=0 && i < length; src[srcOffset + i] < dest[destOffset + i] &&
                 (\forall short j; j>=0 && j<i; src[srcOffset + j] == dest[destOffset + j]));
           ensures \result == 1 ==>
              (\exists short i; i>=0 && i < length; src[srcOffset + i] > dest[destOffset + i] &&
                 (\forall short j; j>=0 && j<i; src[srcOffset + j] == dest[destOffset + j]));
           assignable \nothing;
    @*/
    public static final byte arrayCompare(/*@ nullable @*/ byte[] src, short srcOffset,
            /*@ nullable @*/ byte[] dest, short destOffset, short length)
            throws NullPointerException, ArrayIndexOutOfBoundsException {
         if (src == null || dest == null)
            throw JCSystem.npe;
         if (length < 0 || srcOffset < 0 || destOffset < 0
                || srcOffset  > (short)(src.length - length)
                || destOffset > (short)(dest.length - length))
            throw JCSystem.aioobe;

        if(src == dest && srcOffset == destOffset) {
          return (byte)0;
        }

        /*@ loop_invariant i>=0 && i <= length &&
               (\forall short j; j>=0 && j < i; src[srcOffset + j] == dest[destOffset + j]);
            decreases length - i;
            assignable \nothing;
          @*/
        for(short i=0; i<length; i++) {
           if(src[srcOffset + i] < dest[destOffset + i]) {
              return (byte)-1;
           }
           if(src[srcOffset + i] > dest[destOffset + i]) {
              return (byte)1;
           }
        }
        return (byte)0;
    }
}
