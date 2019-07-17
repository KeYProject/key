package java.util;

public class ArrayList implements java.util.List {

    /*@ public normal_behavior
      @ ensures seq.length == 0;
      @ determines this, seq \by \nothing;
      @*/
    public /*@pure@*/ ArrayList();
}