package java.lang;

public final class StringBuilder implements java.io.Serializable, java.lang.Appendable {
    
    public String str = "";
    
	public StringBuilder() { }
	
    public StringBuilder(int param0) { }
   
    /*@ public normal_behavior
      @ ensures \fresh(str) && str != null;
      @ ensures \result == this;
      @ assignable str;
      @ determines str \by str, param0;
      @*/
    public java.lang.StringBuilder append(char param0);
    
    /*@ public normal_behavior
      @ ensures \result == str;
      @ assignable \nothing;
      @ determines \result \by str;
      @*/
    public String toString() {
        return str;
    }
}