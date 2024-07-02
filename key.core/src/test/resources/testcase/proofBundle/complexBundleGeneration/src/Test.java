import java.util.List;
import java.io.InputStream;

public class Test {
    // check that all of these classes are correctly loaded:
    // bootclasspath
    Object o;
    String str;
    List l;
    InputStream is;

    // classpath
    A a;        // *.class
    B b;        // *.java
    C1 c1;      // loading from a zip
    C2 c2;      // loading from a zip
    D d;        // *.java

    // javaSource
    Client cl;

    /*@ normal_behavior
      @ requires true;
      @ ensures true;
      @*/
    public void trivial() {
    }

    /*@ normal_behavior
      @ requires d != null;
      @ requires \invariant_for(d);
      @ ensures \result == 5;
      @*/
    public int constant() {
        return d.constant();
    }
}
