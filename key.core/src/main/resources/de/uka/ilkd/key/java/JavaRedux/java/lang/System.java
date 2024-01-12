package java.lang;

public final class System {

    public static final java.io.InputStream in;
    public static final java.io.PrintStream out;
    public static final java.io.PrintStream err;

    // Remarks: Currently the specifications assumes src and dest to be int[].
    //          This is incomplete, and should be amended when needed
    // added by Mattias Ulbrich in Jan 19.
    /*@ public exceptional_behavior
      @   requires src == null || dest == null;
      @   signals_only NullPointerException;
      @   assignable \nothing;
      @ also
      @ public exceptional_behavior
      @   requires src instanceof int[] && dest instanceof int[];
      @   requires src != null && dest != null;
      @   requires (srcPos < 0 || destPos < 0 || length < 0
      @                  || srcPos + length > ((int[])src).length
      @                  || destPos + length > ((int[])dest).length);
      @    assignable \nothing;
      @    signals_only ArrayIndexOutOfBoundsException;
      @ also
      @ public normal_behavior
      @   requires src instanceof int[] && dest instanceof int[];
      @   requires src != null && dest != null;
      @   requires srcPos >= 0 && destPos >= 0;
      @   requires length >= 0;
      @   requires srcPos + length <= ((int[])src).length
      @         && destPos + length <= ((int[])dest).length;
      @   ensures (\forall int i; 0 <= i && i < length;
      @             ((int[])dest)[destPos + i] == \old(((int[])src)[srcPos + i]));
      @   assignable ((int[])dest)[destPos .. destPos + length - 1];
      @*/
    /*@ helper @*/
    public static native void arraycopy(/*@nullable*/ java.lang.Object src,  int  srcPos,
                                        /*@nullable*/ java.lang.Object dest, int destPos,
                                        int length);
    // This implementation has been used to verify the above contracts
    // {
    //     if(src == null || dest == null) {
    //         throw new NullPointerException();
    //     }
    //     int[] isrc = (int[])src;
    //     int[] idest = (int[])dest;
    //     if(length < 0) {
    //         throw new ArrayIndexOutOfBoundsException();
    //     }
    //     int[] tmp = new int[length];
    //     if(srcPos < 0 || srcPos + length > isrc.length) {
    //         throw new ArrayIndexOutOfBoundsException();
    //     }
    //     /*@ loop_invariant 0 <= i && i <= length;
    //       @ loop_invariant (\forall int j; 0<=j && j < i; tmp[j] == isrc[srcPos + j]);
    //       @ loop_invariant \fresh(tmp);
    //       @ decreases length - i;
    //       @ assignable tmp[*];
    //       @*/
    //     for(int i = 0; i < length; i++) {
    //         tmp[i] = isrc[srcPos + i];
    //     }
    //     if(destPos < 0 || destPos + length > idest.length) {
    //         throw new ArrayIndexOutOfBoundsException();
    //     }
    //     /*@ loop_invariant 0 <= k && k <= length;
    //       @ loop_invariant (\forall int j; 0<=j && j < k; idest[destPos + j] == tmp[j]);
    //       @ decreases length - k;
    //       @ assignable idest[destPos .. destPos + length - 1];
    //       @*/
    //     for(int k = 0; k < length; k++) {
    //         idest[destPos + k] = tmp[k];
    //     }
    // }

    /*@ public behavior
      @ ensures false;
      @ signals_only \nothing;
      @ diverges true;
      @*/
    public static void exit(int code);
}
