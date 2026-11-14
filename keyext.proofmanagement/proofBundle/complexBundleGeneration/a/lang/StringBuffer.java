package java.lang;

public class StringBuffer extends java.lang.Object implements java.io.Serializable
						    //, CharSequence 
{
    public StringBuffer();
    public StringBuffer(int n);
    public StringBuffer(java.lang.String s);

    public StringBuffer	append(boolean b); 
    public StringBuffer	append(char c); 
    //    public StringBuffer	append(char[] str); 
    //    public StringBuffer	append(char[] str, int offset, int len); 
    //    public StringBuffer	append(double d); 
    //    public StringBuffer	append(float f); 
    public StringBuffer	append(int i); 
    public StringBuffer	append(long l); 
    public StringBuffer	append(java.lang.Object obj); 
    public StringBuffer	append(java.lang.StringBuffer sb); 

    public char charAt(int index) ;
    public int length();
    //    public CharSequence subSequence(int start, int end);
    java.lang.String toString();
 }
