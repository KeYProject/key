/* Golden M3 fixture: the exact source shape the KeY JVM transpiler emits for SwitchClass --
 * tableswitch/lookupswitch: pop the selector into a plain int temp, dispatch as an if-chain of
 * `if (sel == key) { jvm.Local.goto_(pc); }` over the dense key range (tableswitch) / sparse
 * key list (lookupswitch), then an unconditional goto_(dflt). Every case/default becomes a
 * guarded L<pc> block; each case body is a mid-layout return (if (true) { return stk.top(); })
 * or the trailing labeled return. Completed with the JML contracts of the original methods.
 *
 * Unlike the object slices, the switch proof is int-only (no Object-typed stack op), so it
 * closes under DefaultAutoMacro -- SwitchProofTest gates classify and lookup. */
public class SwitchClass {

    /*@ public normal_behavior
      @   assignable \nothing;
      @   ensures \result == (x == 0 ? 10 : (x == 1 || x == 2 ? 20 : 30));
      @*/
    public static int classify(int x) {
        jvm.Local stk = new jvm.Local();
        stk.push(x);
        int $s0 = stk.pop();
        if ($s0 == 0) { jvm.Local.goto_(4); }
        if ($s0 == 1) { jvm.Local.goto_(9); }
        if ($s0 == 2) { jvm.Local.goto_(9); }
        jvm.Local.goto_(14);
        L4: { if (false) { break L4; }
        stk.push(10);
        if (true) { return stk.top(); }
        }
        L9: { if (false) { break L9; }
        stk.push(20);
        if (true) { return stk.top(); }
        }
        L14: { if (false) { break L14; }
        stk.push(30);
        return stk.top();
        }
        return 0;
    }

    /*@ public normal_behavior
      @   assignable \nothing;
      @   ensures \result == (x == 7 ? 70 : (x == 100 ? 100 : -1));
      @*/
    public static int lookup(int x) {
        jvm.Local stk = new jvm.Local();
        stk.push(x);
        int $s0 = stk.pop();
        if ($s0 == 7) { jvm.Local.goto_(4); }
        if ($s0 == 100) { jvm.Local.goto_(9); }
        jvm.Local.goto_(14);
        L4: { if (false) { break L4; }
        stk.push(70);
        if (true) { return stk.top(); }
        }
        L9: { if (false) { break L9; }
        stk.push(100);
        if (true) { return stk.top(); }
        }
        L14: { if (false) { break L14; }
        stk.push(-1);
        return stk.top();
        }
        return 0;
    }

}
