package java.lang;

public final class StringBuilder implements java.io.Serializable, java.lang.Appendable {
    
    public String string = "";
    
	public StringBuilder() { }
	
    public StringBuilder(int param0) { }
   
    public java.lang.StringBuilder append(char param0) {
        string = string + param0;
    }
    
    public String toString() {
        return string;
    }
}