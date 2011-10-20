package javacard.framework;

public class Util {

    /*@
         public transaction behavior
           requires JCSystem.npe != null;
           requires JCSystem.aioobe != null;
           requires JCSystem.isTransient(dest) != JCSystem.NOT_A_TRANSIENT_OBJECT ==> !\transactionUpdated(dest);
           ensures \result == destOffset + length;
           ensures (\forall short i; i>=0 && i<length; dest[destOffset + i] == \old(src[srcOffset + i]));
           ensures (JCSystem.isTransient(dest) == JCSystem.NOT_A_TRANSIENT_OBJECT && \transactionUpdated(dest)) ?  
              (\forall short i; i>=0 && i<length; \backup(dest[destOffset + i]) == \old(\backup(dest[destOffset + i])))
            : (\forall short i; i>=0 && i<length; \backup(dest[destOffset + i]) == \old(src[srcOffset + i]));
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
               (\forall short j; j>=0 && j<i; dest[destOffset + j] == \old(src[srcOffset + j])) &&
               (\forall short j; j>=i && j<length; dest[destOffset + j] == \old(dest[destOffset + j]));
             loop_invariant_transaction
                 (\transactionUpdated(dest) ?
                   (\forall short j; j>=0 && j<i; \backup(dest[destOffset + j]) == \old(\backup(dest[destOffset + j])))
                 :
                   (\forall short j; j>=0 && j<i; \backup(dest[destOffset + j]) == \old(src[srcOffset + j])))
               && (\forall short j; j>=i && j<length; \backup(dest[destOffset + j]) == \old(\backup(dest[destOffset + j])));
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
                srcOffset + length - i >= 0 && srcOffset + length - i <= src.length &&
                destOffset + length - i >= 0 && destOffset + length - i <= dest.length &&
                (\forall short j; j >= 0 && j < length - i; dest[destOffset + j] == \old(dest[destOffset + j])) && 
                (\forall short j; j >= length - i && j < length; dest[destOffset + j] == \old(src[srcOffset + j]))
             ;
             loop_invariant_transaction
                 (\transactionUpdated(dest) ?
                   (\forall short j; j >= 0 && j < length - i;
                        \backup(dest[destOffset + j]) == \old(\backup(dest[destOffset + j])))
                 :
                   (\forall short j; j >= length - i && j < length; \backup(dest[destOffset + j]) == \old(src[srcOffset + j])))
               && (\forall short j; j >= 0 && j < length - i;
                                \backup(dest[destOffset + j]) == \old(\backup(dest[destOffset + j])));
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
