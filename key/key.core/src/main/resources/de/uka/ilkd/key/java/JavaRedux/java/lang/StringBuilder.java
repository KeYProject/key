package java.lang;

public final class StringBuilder implements java.io.Serializable, java.lang.Appendable {
    
    public String str = "";
    
    /*@ public normal_behavior
      @ ensures \fresh(this) && \fresh(this.*);
      @ assignable str;
      @ determines this, str \by \nothing \new_objects this, str;
      @ determines \dl_strContent(str) \by \nothing;
      @*/
	public StringBuilder();
	
	/*@ public normal_behavior
      @ ensures \fresh(this) && \fresh(this.*);
      @ assignable str;
      @ determines this, str \by \nothing \new_objects this, str;
      @ determines \dl_strContent(str) \by \nothing;
      @*/
    public StringBuilder(int param0);
   
    /*@ public normal_behavior
      @ ensures \fresh(str) && str != null;
      @ ensures \result == this;
      @ assignable str;
      @ determines str \by \nothing \new_objects str;
      @ determines \dl_strContent(str) \by \dl_strContent(str), param0;
      @*/
    public java.lang.StringBuilder append(char param0);
    
    /*@ public normal_behavior
      @ ensures \result == str;
      @ assignable \nothing;
      @ determines \result \by str;
      @ determines \dl_strContent(\result) \by \dl_strContent(str);
      @*/
    public String toString() {
        return str;
    }
}