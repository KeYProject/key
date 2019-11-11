package org.apache.commons.csv;

public final class CSVRecord extends java.lang.Object implements java.io.Serializable, java.lang.Iterable {
    
    //@ public instance ghost \seq key_seq;
    //@ public instance ghost \seq value_seq;
    
    //@ public instance invariant key_seq.length == value_seq.length;
    //@ public instance invariant (\forall int i; 0 <= i && i < key_seq.length; ((String)key_seq[i]) != null);
    //@ public instance invariant (\forall int i; 0 <= i && i < value_seq.length; ((String)value_seq[i]) != null);

    /*@ public normal_behavior
      @ requires  (\exists \bigint i; 0 <= i && i < key_seq.length; ((String)key_seq[i]) == param0);
      @ ensures   (\exists \bigint i; 0 <= i && i < key_seq.length; ((String)key_seq[i]) == param0 && ((String)value_seq[i]) == \result);
      @ assignable \strictly_nothing;
      @ determines \result \by key_seq, value_seq, \dl_strContent(param0);
      @*/
    public java.lang.String get(java.lang.String param0);
}