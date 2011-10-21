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
                 ((JCSystem.isTransient(dest) == JCSystem.NOT_A_TRANSIENT_OBJECT && \transactionUpdated(dest)) ?  
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
    public static short arrayCopyNonAtomic(/*@ nullable @*/ byte[] src, short srcOffset,
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
                    ((j >= i || \transactionUpdated(dest)) ?
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
                    ((j < length - i || \transactionUpdated(dest)) ?
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

}
