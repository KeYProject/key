package java.lang;

public final class StringBuilder implements java.io.Serializable, java.lang.Appendable {
    
    public String str;
    
    /*@ public normal_behavior
      @ ensures \fresh(this) && \fresh(str) && \typeof(this) == \type(StringBuilder) && \typeof(str) == \type(String);
      @ determines str \by \nothing \new_objects str;
      @ determines \dl_strContent(str) \by \nothing;
      @*/
	public /*@pure@*/ StringBuilder();
	
	/*@ public normal_behavior
      @ ensures \fresh(this) && \fresh(str) && \typeof(this) == \type(StringBuilder) && \typeof(str) == \type(String);
      @ determines str \by \nothing \new_objects str;
      @ determines \dl_strContent(str) \by \nothing;
      @*/
    public /*@pure@*/ StringBuilder(int param0);
   
    /*@ public normal_behavior
      @ ensures \fresh(str) && str != null && \typeof(str) == \type(String);
      @ ensures \result == this;
      @ ensures \fresh(str);
      @ assignable str;
      @ determines str \by \nothing \new_objects str;
      @ determines \dl_strContent(str) \by \dl_strContent(str), param0;
      @*/
    public java.lang.StringBuilder append(char param0);
    
    public String toString() {
        return str;
    }
}