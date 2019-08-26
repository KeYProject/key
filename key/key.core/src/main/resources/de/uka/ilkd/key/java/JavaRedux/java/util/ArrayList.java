package java.util;

public final class ArrayList implements java.util.List {

    /*@ public normal_behavior
      @ ensures seq.length == 0;
      @ determines this, seq \by \nothing;
      @*/
    public /*@pure@*/ ArrayList();

    /*@ public normal_behavior
      @ ensures seq == c.seq;
      @ determines this, seq \by c.seq;
      @*/
    public /*@pure@*/ ArrayList(Collection c);
}