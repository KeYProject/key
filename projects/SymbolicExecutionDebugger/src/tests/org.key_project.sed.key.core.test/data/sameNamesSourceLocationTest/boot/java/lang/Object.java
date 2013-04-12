package java.lang;

public class Object {  

    
    /*@ public normal_behavior
      @   assignable \nothing;
      @*/
    public /*@ pure @*/ Object() {}
    

    public /*@ pure @*/ boolean equals(java.lang.Object o);
    public int hashCode();


}
