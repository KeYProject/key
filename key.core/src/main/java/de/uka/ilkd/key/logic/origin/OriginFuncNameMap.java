package de.uka.ilkd.key.logic.origin;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.op.ProgramVariable;

import java.util.HashMap;
import java.util.Map;

/**
 * Maps function names to their original ProgramVariables
 */
public class OriginFuncNameMap {

    private final Map<Name, ProgramVariable> map = new HashMap<>();

    private final Object lock = new Object();

    public void put(ProgramVariable src, Name repl) {
        synchronized (lock) {
            map.put(repl, src);
        }
    }

    public ProgramVariable get(Name repl) {
        synchronized (lock) {
            return map.get(repl);
        }
    }

    public boolean has(Name repl) {
        synchronized (lock) {
            return map.containsKey(repl);
        }
    }
}
