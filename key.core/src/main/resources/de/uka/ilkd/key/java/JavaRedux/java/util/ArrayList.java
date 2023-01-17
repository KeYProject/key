package java.util;

public final class ArrayList implements java.util.List {

    /*@ public normal_behavior
      @ ensures seq.length == 0;
      @ ensures \fresh(this) && \fresh(this.*);
      @ determines seq \by \nothing;
      @*/
    public /*@pure@*/ ArrayList();

    /*@ public normal_behavior
      @ ensures seq == c.seq;
      @ ensures \fresh(this) && \fresh(this.*) && \typeof(this) == \type(ArrayList);
      @ determines this, seq \by c.seq \new_objects this;
      @*/
    public /*@pure@*/ ArrayList(Collection c);
}