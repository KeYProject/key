package java.lang;

public final class StringBuilder implements java.io.Serializable, java.lang.Appendable {
    
    public String string = "";
    
	public StringBuilder() { }
	
    public StringBuilder(int param0) { }
   
    /*@ public normal_behavior
      @ ensures \fresh(string) && string != null;
      @ ensures \result == this;
      @ assignable string;
      @ determines string \by string, param0;
      @*/
    public java.lang.StringBuilder append(char param0);
    
    public String toString() {
        return string;
    }
}