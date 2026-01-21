package java.lang;

public final class String extends java.lang.Object implements java.io.Serializable, java.lang.Comparable
{
   // public final static java.util.Comparator CASE_INSENSITIVE_ORDER;

   /*@ normal_behavior
       ensures \result == \dl_seqLen(\dl_strContent(this));
    */
   public /*@pure*/ int length();


   /*@
   public normal_behavior
      requires true;
      ensures \dl_strContent(this)==\dl_seqEmpty();
      assignable \nothing;
    */
   public String();

   /*@
   public normal_behavior
      requires other != null;
      ensures \dl_strContent(this)==\dl_strContent(other);
      assignable \nothing;
   also
   public exceptional_behavior
      requires other == null;
      signals (java.lang.NullPointerException) true;
      assignable \nothing;
   */
   public String(java.lang.String other);


   /*@
   public normal_behavior
      requires v != null;
      ensures \dl_seqLen ( \dl_strContent(this)) == v.length
          && (\forall int i; i >= 0 && i < v.length;
               (int) \dl_strContent(this)[i] == v[i]);
      assignable \nothing;
   also
   public exceptional_behavior
      requires v == null;
      signals (java.lang.NullPointerException) true;
      assignable \nothing;
   */
   public String(char[] v);


   /*@
   public normal_behavior
      requires v != null;
      requires offset >= 0 && count >= 0 && offset + count <= v.length;
      ensures \dl_seqLen(\dl_strContent(this))==count;
      ensures (\forall int i; i >= 0 && i < count;
                     v[offset+i] == (int) \dl_strContent(this)[i]);
      assignable \nothing;
   also
   public exceptional_behavior
      requires v != null;
      requires (offset < 0 || count < 0 || offset + count > v.length);
      signals (java.lang.IndexOutOfBoundsException) true;
      assignable \nothing;
   also
   public exceptional_behavior
      requires v == null;
      signals (java.lang.NullPointerException) true;
      assignable \nothing;
   */
   public String(char[] v, int offset, int count);
   public String(int[] arg0, int arg1, int arg2);
   public String(byte[] arg0, int arg1, int arg2, int arg3);
   public String(byte[] arg0, int arg1);
// public String(byte[] arg0, int arg1, int arg2, java.lang.String arg3) throws java.io.UnsupportedEncodingException;
// public String(byte[] arg0, int arg1, int arg2, java.nio.charset.Charset arg3);
// public String(byte[] arg0, java.lang.String arg1) throws java.io.UnsupportedEncodingException;
// public String(byte[] arg0, java.nio.charset.Charset arg1);
   public String(byte[] arg0, int arg1, int arg2);
   public String(byte[] arg0);
// public String(java.lang.StringBuffer arg0);
// public String(java.lang.StringBuilder arg0);

   /*@
   public normal_behavior
      requires true;
      ensures \result==\dl_seqLen(\dl_strContent(this));
      assignable \strictly_nothing;
    */
   public /*@ helper */ int length();

   /*@
   public normal_behavior
      requires true;
      ensures \result <==> \dl_strContent(this) == \dl_seqEmpty();
      assignable \strictly_nothing;
   */
   public /*@ helper */ boolean isEmpty();

   /*@
   public normal_behavior
      requires charIdx >= 0 && charIdx < \dl_strContent(this).length;
      ensures \result==(int) \dl_strContent(this)[charIdx];
      assignable \strictly_nothing;
   also
   public exceptional_behavior
      requires charIdx < 0 || charIdx >= \dl_seqLen(\dl_strContent(this));
      signals (java.lang.IndexOutOfBoundsException) true;
      assignable \strictly_nothing;
    */
   public /*@ helper */ char charAt(int charIdx);
   public /*@ helper */ int codePointAt(int arg0);
   public /*@ helper */ int codePointBefore(int arg0);
   public /*@ helper */ int codePointCount(int arg0, int arg1);
   public /*@ helper */ int offsetByCodePoints(int arg0, int arg1);
   /*@
   public normal_behavior
      requires dst != null && srcBegin >= 0 && srcBegin <= srcEnd
               && srcEnd <= \dl_seqLen(\dl_strContent(this))
               && dstBegin >= 0
               && dstBegin + (srcEnd - srcBegin) <= dst.length;
      ensures (\forall int i;
                     0 <= i < (srcEnd - srcBegin)
                  && (int) \dl_strContent(this)[srcBegin + i] == dst[dstBegin + i]
                  && (0 <= i  && i < dstBegin ==> dst[i] == \old(dst[i]))
                  && (dstBegin + (srcEnd - srcBegin) <= i < dst.length);
			    dst[i] == \old(dst[i]));
      assignable dst[*];
   also
   public exceptional_behavior
      requires dst != null && (  srcBegin < 0
             || srcBegin > srcEnd
             || srcEnd > \dl_seqLen(\dl_strContent(this))
             || dstBegin < 0
             || dstBegin + (srcEnd - srcBegin) > dst.length);
      signals (java.lang.IndexOutOfBoundsException) true;
      assignable \strictly_nothing;
   also
   public exceptional_behavior
      requires dst == null;
      signals (java.lang.NullPointerException) true;
      assignable \strictly_nothing;
    */
   public void getChars(int srcBegin, int srcEnd, char[] dst, int dstBegin);

   public void getBytes(int arg0, int arg1, byte[] arg2, int arg3);
// public byte[] getBytes(java.lang.String arg0) throws java.io.UnsupportedEncodingException;
// public byte[] getBytes(java.nio.charset.Charset arg0);

   /*@ public normal_behavior
     @ ensures \fresh(\result) && \typeof(\result) == \type(byte[]);
     @ assignable \nothing;
     @ determines \result \by \nothing \new_objects \result;
     @ determines \result[*] \by \dl_strContent(this);
     @*/
   public /*@ helper */ byte[] getBytes();

   /*@
   public normal_behavior
   requires true;
   ensures \result <==> obj != null
          && obj instanceof java.lang.String
          && \dl_strContent(this)==\dl_strContent((java.lang.String)obj);
   assignable \strictly_nothing;
   */
   public /*@ helper */ boolean equals(/*@ nullable */ java.lang.Object obj);
// public boolean contentEquals(java.lang.StringBuffer arg0);
// public boolean contentEquals(java.lang.CharSequence arg0);
   public /*@ helper */ boolean equalsIgnoreCase(java.lang.String arg0);
   public /*@ helper */ int compareTo(java.lang.String arg0);
   public /*@ helper */ int compareToIgnoreCase(java.lang.String arg0);
   public /*@ helper */ boolean regionMatches(int arg0, java.lang.String arg1, int arg2, int arg3);
   public /*@ helper */ boolean regionMatches(boolean arg0, int arg1, java.lang.String arg2, int arg3, int arg4);

   /*@
   public normal_behavior
      requires other != null;
      ensures \result <==>
                              startIdx >= 0
                           && (startIdx <= \dl_seqLen(\dl_strContent(this)))
                           && \dl_clStartsWith(
                                 \dl_seqSub(
                                    \dl_strContent(other), startIdx,
                                    \dl_seqLen(\dl_strContent(this))
                                 ),
                                 \dl_strContent(other)
                             );
      assignable \strictly_nothing;
   also
   public exceptional_behavior
      requires other == null;
      signals (java.lang.NullPointerException) true;
      assignable \nothing;
   */
   public boolean /*@ helper */ startsWith(/*@ nullable*/ java.lang.String other, int startIdx);

   /*@
   public normal_behavior
      requires other != null;
      ensures \result <==> \dl_clStartsWith(\dl_strContent(this), \dl_strContent(other));
      assignable \strictly_nothing;
   also
   public exceptional_behavior
      requires other == null;
      signals (java.lang.NullPointerException) true;
      assignable \nothing;
    */
   public boolean /*@ helper */ startsWith(java.lang.String other);

   /*@
   public normal_behavior
      requires other  != null;
      ensures \result <==> \dl_clEndsWith(\dl_strContent(this), \dl_strContent(other));
      assignable \strictly_nothing;
   also
   public exceptional_behavior
      requires other == null;
      signals (java.lang.NullPointerException) true;
      assignable \strictly_nothing;
    */
   public /*@ helper */ boolean endsWith(java.lang.String other);

   /*@
   public normal_behavior
      requires true;
      ensures \result == \dl_clHashCode(\dl_strContent(this));
      assignable \strictly_nothing;
   */
   public /*@ helper */ int hashCode();
   /*@
   public normal_behavior
      requires true;
      ensures \result==\dl_clIndexOfChar( \dl_strContent(this), charVal, 0);
      assignable \strictly_nothing;
   */
   public /*@ helper */ int indexOf(int charVal) { return indexOf(charVal, 0); }

   /*@
   public normal_behavior
      requires true;
      ensures \result == \dl_clIndexOfChar(\dl_strContent(this), charVal, from);
      assignable \strictly_nothing;
   */
   public /*@ helper */ int indexOf(int charVal, int from);

   /* @
   public normal_behavior
      requires true;
      ensures \result == \dl_clLastIndexOfChar(
                  \dl_strContent(this), charVal,
                  \dl_seqLen(\dl_strContent(this)) - 1));
      assignable \strictly_nothing;
   */
   public /*@ helper */ int lastIndexOf(int charVal) { return lastIndexOf(charVal, 0); }

   public /*@ helper */ int lastIndexOf(int charVal, int from);

   public /*@ helper */ int indexOf(java.lang.String other) { return indexOf(other, 0); }

   /*@
   public normal_behavior
      requires t != null;
      ensures \result == \dl_clIndexOfCl(\dl_strContent(this), from, \dl_strContent(t));
      assignable \strictly_nothing;
   also
      public exceptional_behavior
      requires t==null;
      signals (java.lang.NullPointerException) true;
      assignable \strictly_nothing;
   */
   public /*@ helper */ int indexOf(java.lang.String t, int from);

   /*@
   public normal_behavior
      requires other != null;
      ensures \result ==
                  \dl_clLastIndexOfCl(
                     \dl_strContent(this),
                     \dl_seqLen(\dl_strContent(this)) - 1,
                     \dl_strContent(other));

      assignable \strictly_nothing;
   also
   public exceptional_behavior
      requires other == null;
      signals (java.lang.NullPointerException) true;
      assignable \nothing;
   */
   public /*@ helper */ int lastIndexOf(java.lang.String other);

   /*@
   public normal_behavior
      requires other != null;
      ensures \result ==
                  \dl_clLastIndexOfCl(\dl_strContent(this), from, \dl_strContent(other));
      assignable \strictly_nothing;
   also
   public exceptional_behavior
      requires other == null;
      signals (java.lang.NullPointerException) true;
      assignable \nothing;
   */
   public /*@ helper */ int lastIndexOf(java.lang.String other, int from);

   /*@
   public normal_behavior
      requires startIdx >= 0 && startIdx < \dl_seqLen(\dl_strContent(this));
      //boolean::select(heapAtPre, \result, java.lang.Object::<created>)==FALSE
      ensures \result != null;
      ensures \dl_strContent(\result)==\dl_seqSub(\dl_strContent(this), startIdx, \dl_seqLen(\dl_strContent(this)));
      assignable \nothing;
   also
   public exceptional_behavior
      requires startIdx < 0 || startIdx > \dl_seqLen(\dl_strContent(this));
      signals (java.lang.IndexOutOfBoundsException) true;
      assignable \nothing;
   */
   public /*@ helper */ java.lang.String substring(int startIdx);


   /*@
   public normal_behavior
      requires endIdx >= startIdx && startIdx >= 0
           && endIdx <= \dl_seqLen(\dl_strContent(this));
      //boolean::select(heapAtPre, result, java.lang.Object::<created>)==FALSE
      ensures \result != null;
      ensures \dl_strContent(\result)==\dl_seqSub(\dl_strContent(this), startIdx, endIdx);
      assignable \nothing;
   also
   public exceptional_behavior
      requires startIdx > endIdx || startIdx < 0 || endIdx > \dl_seqLen(\dl_strContent(this));
      signals (java.lang.IndexOutOfBoundsException) true;
      assignable \nothing;
    */
   public /*@ helper */ java.lang.String substring(int startIdx, int endIdx);
// public java.lang.CharSequence subSequence(int arg0, int arg1);

   /*@
   public normal_behavior
      requires    other != null;
      requires \dl_seqLen(\dl_strContent(other)) > 0;
      //ensures boolean::select(heapAtPre, result, java.lang.Object::<created>)==FALSE
      ensures \result != null;
      ensures \dl_strContent(\result)==\dl_seqConcat(\dl_strContent(this), \dl_strContent(other));
      assignable \nothing;
    also
    public normal_behavior
      requires    other != null;
      requires \dl_seqLen(\dl_strContent(other))==0;
      ensures \result == this;
      assignable \nothing;
    also
    public exceptional_behavior
      requires other == null;
      signals (java.lang.NullPointerException) true;
      assignable \nothing;
    */
   public java.lang.String concat(java.lang.String other);


   /*@
   public normal_behavior
      requires true;
      ensures
         (\exists int i;
            i >= 0 && i < \dl_seqLen(\dl_strContent(this));
            (int) \dl_strContent(this)[i] == c1)
         ? \result != null && \dl_strContent(\result) == \dl_clReplace(\dl_strContent(this), c1, c2)
         : \result == this;
      assignable \nothing;
   */
   public java.lang.String replace(char c1, char c2);
   public boolean matches(java.lang.String arg0);
// public boolean contains(java.lang.CharSequence arg0);
   public java.lang.String replaceFirst(java.lang.String arg0, java.lang.String arg1);
   public java.lang.String replaceAll(java.lang.String arg0, java.lang.String arg1);
// public java.lang.String replace(java.lang.CharSequence arg0, java.lang.CharSequence arg1);
   public java.lang.String[] split(java.lang.String arg0, int arg1);
   public java.lang.String[] split(java.lang.String arg0);
// public java.lang.String toLowerCase(java.util.Locale arg0);

   /*@ public normal_behavior
     @ ensures \fresh(\result) && \typeof(\result) == \type(String);
     @ assignable \nothing;
     @ determines \result \by \nothing \new_objects \result;
     @ determines \dl_strContent(\result) \by \dl_strContent(this);
     @*/
   public java.lang.String toLowerCase();
// public java.lang.String toUpperCase(java.util.Locale arg0);

   /*@ public normal_behavior
     @ ensures \fresh(\result) && \typeof(\result) == \type(String);
     @ assignable \nothing;
     @ determines \result \by \nothing \new_objects \result;
     @ determines \dl_strContent(\result) \by \dl_strContent(this);
     @*/
   public java.lang.String toUpperCase();
   /*@
   public normal_behavior
      requires true;
      ensures \result != null;
      ensures \dl_strContent(\result).length <= \dl_strContent(this).length;
      assignable \nothing;
   also
      public normal_behavior
      requires (\exists int i;
               (0 <= i & i < \dl_strContent(this).length
                     && ((char)\dl_strContent(this)[i]) > '\u0020'));
      ensures \result != null;
      ensures \dl_strContent(\result).length <= \dl_strContent(this).length;
      ensures \dl_strContent(\result).length >= 1;
      assignable \nothing;
    */
   public java.lang.String trim();

   /*@
   public normal_behavior
      requires true;
      ensures \result == this;
      assignable \strictly_nothing;
   */
   public java.lang.String toString();

   /*@ public normal_behavior
     @ ensures \result.length == \dl_strContent(this).length;
     @ ensures (\forall \bigint i; 0 <= i && i < \result.length; \dl_inChar(\result[i]));
     @ ensures \fresh(\result) && \typeof(\result) == \type(char[]);
     @ assignable \nothing;
     @ determines \result \by \nothing \new_objects \result;
     @ determines \result[*] \by \dl_strContent(this);
     @*/
   public char[] toCharArray();

   public static java.lang.String format(java.lang.String arg0, java.lang.Object[] arg1);
// public static java.lang.String format(java.util.Locale arg0, java.lang.String arg1, java.lang.Object[] arg2);

   /*@
   public normal_behavior
      requires obj == null;
      ensures \dl_strContent(\result) == "null";
      ensures \result != null;
      //       && boolean::select(heapAtPre, \result, java.lang.Object::<created>)==FALSE
      assignable \nothing;
   also
   public normal_behavior
      requires obj != null;
      ensures \result==obj.toString();
      assignable \nothing;
   //also
   //public normal_behavior
   //   requires obj != null && obj instanceof Boolean;
   //   ensures \dl_strContent(\result) == (obj == true ? "true" : "false");
   //   ensures \result != null;
   //   assignable \strictly_nothing;
   also
   public normal_behavior
      requires obj!=null && obj instanceof java.lang.Character;
      ensures \dl_strContent(\result) == \dl_seqSingleton((char) obj);
      ensures \result != null;
      assignable \nothing;
   also
   public normal_behavior
      requires obj!=null && obj instanceof java.lang.Integer;
      ensures \dl_strContent(\result)==\dl_clRemoveZeros(\dl_clTranslateInt((int) obj));
      ensures \result != null;
      assignable \nothing;
   also
   public normal_behavior
      requires obj!=null && obj instanceof java.lang.Long;
      ensures \dl_strContent(\result)==\dl_clRemoveZeros(\dl_clTranslateInt((long) obj));
      ensures \result != null;
      assignable \nothing;
  */
   public static java.lang.String valueOf(java.lang.Object obj);

   /*@
   public normal_behavior
      requires (data != null);
      ensures (\forall int i; 0<= i < data.length;
                  (int) \dl_strContent(\result)[i]==data[i]);
      ensures \dl_seqLen(\dl_strContent(\result))==data.length;
      ensures \result != null;
      assignable \nothing;
   also
   public exceptional_behavior
      requires data == null;
      signals (java.lang.NullPointerException) true;
      assignable \nothing;
   */
   public static java.lang.String valueOf(char[] data);

   /*@
   public normal_behavior
      requires data != null && offset >= 0 && count >= 0
               && offset + count <= data.length;
      ensures (\forall int i; 0<= i && i < count;
                  (int) \dl_strContent(\result)[i] == data[offset + i]);
      ensures \dl_seqLen(\dl_strContent(\result)) == count;
      ensures \result != null;
      assignable \nothing;
   also
   public exceptional_behavior
      requires data != null;
      requires offset < 0 || count < 0 || offset+count > data.length;
      signals (java.lang.IndexOutOfBoundsException) true;
      assignable \nothing;
   also
   public exceptional_behavior
      requires data == null;
      signals (java.lang.NullPointerException) true;
      assignable \nothing;
   */
   public static java.lang.String valueOf(char[] data, int offset, int count);


   /*@
    public normal_behavior
      requires data != null;
      requires offset >= 0 && count >= 0 && offset+count <= data.length;
      ensures \dl_seqLen(\dl_strContent(\result)) == count;
      ensures (\forall int i; 0 <= i < count;
                         (int) \dl_strContent(\result)[i] == data[i+offset]);
      //    && boolean::select(heapAtPre, \result, java.lang.Object::<created>)==FALSE
      ensures \result != null;
      assignable \nothing;
   also
   public exceptional_behavior
      requires data != null;
      requires offset < 0 || count < 0 || offset+count > data.length;
      signals (java.lang.IndexOutOfBoundsException) true;
      assignable \nothing;
   also
   public exceptional_behavior
      requires data == null;
      signals (java.lang.NullPointerException) true;
      assignable \nothing;
    */
   public static java.lang.String copyValueOf(char[] data, int offset, int count);

   /*@
   public normal_behavior
      requires data != null;
      ensures \dl_seqLen(\dl_strContent(\result)) == data.length;
      ensures (\forall int i; 0 <= i < data.length;
                  (int) \dl_strContent(\result)[i] == data[i]);
      ensures \result != null;
      //    && boolean::select(heapAtPre, \result, java.lang.Object::<created>)==FALSE
      assignable \nothing;
   also exceptional_behavior
      requires data == null;
      signals (java.lang.NullPointerException) true;
      assignable \nothing;
    */
   public static java.lang.String copyValueOf(char[] data);

   public static java.lang.String valueOf(boolean arg0);
   public static java.lang.String valueOf(char arg0);
   public static java.lang.String valueOf(int arg0);
   public static java.lang.String valueOf(long arg0);
//   public static java.lang.String valueOf(float arg0);
//   public static java.lang.String valueOf(double arg0);

   /*@
   public normal_behavior
      requires true;
      ensures \result != null;
      ensures \result==\dl_strPool(\dl_strContent(this));
      assignable \nothing;
   */
   public java.lang.String intern();


   /*@
   public normal_behavior
     requires other != null && other instanceof java.lang.String;
     ensures
         (\forall int i; 0 <= i < \dl_strContent(this).length
                         && i<\dl_strContent(other).length;
           \dl_strContent(this)[i] == \dl_strContent(other)[i])
         ? \result == \dl_strContent(this).length - \dl_strContent(other).length
         : (\exists int j; (\forall int i; 0 <= i < j; \dl_strContent(this)[i] == \dl_strContent(other)[i])
                           && \result != 0 && \result == (int) \dl_strContent(other)[j] - (int)\dl_strContent(this)[j]);
      assignable \strictly_nothing;
   also
   public exceptional_behavior
      requires other == null;
      signals (java.lang.NullPointerException) true;
      assignable \nothing;
    */
   public int compareTo(java.lang.String other);

   public int compareTo(java.lang.Object other) {
      if(other instanceof String) {
         return compareTo((String) other);
      }
      throw new java.lang.IllegalArgumentException("No string given.");
   }
}
