package java.io;
public class PrintStream /*extends FilterOutputStream implements Closeable, Appendable*/ {
        
        
    //@ public invariant true;

    //@ normal_behavior
    //@ ensures true;
    public /*@ pure @*/ void println();

    protected void setError();

    public boolean checkError();

    //@ normal_behavior
    //@ ensures true;
    public /*@ pure @*/ void print(char c);

    //@ normal_behavior
    //@ ensures true;
    public /*@ pure @*/ void println(char c); 

    //@ normal_behavior
    //@ ensures true;
    public /*@ pure @*/ void println(String s);

    //@ normal_behavior
    //@ ensures true;
    public /*@ pure @*/ void print(String s);

    //@ normal_behavior
    //@ ensures true;
    public /*@ pure @*/ void println(/*@ nullable @*/ Object o);

    //@ normal_behavior
    //@ ensures true;
    public /*@ pure @*/ void print(/*@ nullable @*/ Object o);

    //@ normal_behavior
    //@ ensures true;
    public /*@ pure @*/ void println(boolean b);

    //@ normal_behavior
    //@ ensures true;
    public /*@ pure @*/ void print(boolean Param0);

    //@ normal_behavior
    //@ ensures true;
    public /*@ pure @*/ void print(int Param0);

    //@ normal_behavior
    //@ ensures true;
    public /*@ pure @*/ void println(int i);

    //@ normal_behavior
    //@ ensures true;
    public /*@ pure @*/ void print(long Param0);

    //@ normal_behavior
    //@ ensures true;
    public /*@ pure @*/ void println(long Param0);

    public void flush();

    //@ normal_behavior
    //@ ensures true;
    public /*@ pure @*/ void print(char[] Param0);

    //@ normal_behavior
    //@ ensures true; 
    public /*@ pure @*/ void println(char[] Param0);

    //@ normal_behavior
    //@ ensures true;
    public /*@ pure @*/ void write(int i);

    //@ normal_behavior
    //@ ensures true;
    public /*@ pure @*/ void write(byte[] b, int off, int len);

    public void close();
}
