package java.util;

public final class LinkedHashMap implements java.util.Map {
	
    /*@ public normal_behavior
      @ ensures key_seq.length == 0;
      @ ensures value_seq.length == 0;
      @ assignable \nothing;
      @*/
    public LinkedHashMap();
}