import java.io.InputStream;
import java.util.List;

public class Test {
    // check that all of these classes are correctly loaded:
    // bootclasspath
    Object o;
    String str;
    List l;
    InputStream is;

    // classpath: empty

    // javaSource
    Client cl;

    /*@ normal_behavior
      @ requires true;
      @ ensures true;
      @*/
    public void trivial() {
    }

    /*@ normal_behavior
      @ ensures \result == 5;
      @*/
    public int constant() {
        return 5;
    }
}
