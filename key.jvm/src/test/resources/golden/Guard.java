/* Golden M2 fixture: the exact source shape the KeY JVM transpiler emits for Guard -- the
 * transpiled class references the *external* type Gadget, which is not among the transpiled
 * inputs, so StubGenerator additionally emits default-package golden/Gadget.java-like stub
 * with exactly the accessed members (instance field score for get/putfield, instance method
 * size() for invokevirtual, static field kind for getstatic, static method defaultScore() for
 * invokestatic, and the no-arg constructor for the new+<init> fusion). Completed with the JML
 * contracts of the original methods.
 *
 * The proof side is subject to the Object-typed-op residual of the concept doc §9.1(2)
 * (popRef of the Gadget reference), so no closing gate exists yet; the emitted shape is
 * pinned by TranspileTest. */
public class Guard {

    /*@ public normal_behavior
      @   requires g != null;
      @   assignable \nothing;
      @   ensures \result == g.score;
      @*/
    public static int score(Gadget g) {
        jvm.Local stk = new jvm.Local();
        stk.push(g);
        Gadget $o0 = (Gadget) stk.popRef();
        stk.push($o0.score);
        return stk.top();
    }

    /*@ public normal_behavior
      @   requires g != null;
      @   assignable g.score;
      @   ensures g.score == s;
      @*/
    public static void stamp(Gadget g, int s) {
        jvm.Local stk = new jvm.Local();
        stk.push(g);
        stk.push(s);
        int $v0 = stk.pop();
        Gadget $o1 = (Gadget) stk.popRef();
        $o1.score = $v0;
        return;
    }

    /*@ public normal_behavior
      @   requires g != null;
      @   assignable \nothing;
      @   ensures \result == g.score + g.size();
      @*/
    public static int total(Gadget g) {
        jvm.Local stk = new jvm.Local();
        stk.push(g);
        Gadget $o0 = (Gadget) stk.popRef();
        stk.push($o0.score);
        stk.push(g);
        Gadget $o1 = (Gadget) stk.popRef();
        stk.push($o1.size());
        stk.iadd();
        return stk.top();
    }

    /*@ public normal_behavior
      @   assignable \nothing;
      @   ensures \result == Gadget.kind;
      @*/
    public static int kind() {
        jvm.Local stk = new jvm.Local();
        stk.push(Gadget.kind);
        return stk.top();
    }

    /*@ public normal_behavior
      @   assignable \nothing;
      @   ensures \result == Gadget.defaultScore();
      @*/
    public static int def() {
        jvm.Local stk = new jvm.Local();
        stk.push(Gadget.defaultScore());
        return stk.top();
    }

    /*@ public normal_behavior
      @   assignable \nothing;
      @   ensures \result != null;
      @*/
    public static Gadget fresh() {
        jvm.Local stk = new jvm.Local();
        Gadget $t0 = new Gadget();
        stk.push($t0);
        return (Gadget) stk.topRef();
    }

}
