package de.uka.ilkd.key.logic.origin;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.op.ProgramVariable;

import java.util.HashMap;
import java.util.Map;

public class OriginFuncNameMap { //TODO this should _not_ be static !!!

    private static final Map<Name, ProgramVariable> map = new HashMap<>();

    private static final Object lock = new Object();

    public static void put(ProgramVariable src, Name repl) {
        synchronized (lock) {
            map.put(repl, src);
        }
    }

    public static ProgramVariable get(Name repl) {
        synchronized (lock) {
            return map.get(repl);
        }
    }

    public static boolean has(Name repl) {
        synchronized (lock) {
            return map.containsKey(repl);
        }
    }
}
