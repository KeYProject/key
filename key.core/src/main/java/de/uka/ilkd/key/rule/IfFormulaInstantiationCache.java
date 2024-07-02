package de.uka.ilkd.key.rule;

import java.util.concurrent.locks.ReentrantReadWriteLock;
import java.util.concurrent.locks.ReentrantReadWriteLock.ReadLock;
import java.util.concurrent.locks.ReentrantReadWriteLock.WriteLock;

import org.key_project.util.LRUCache;
import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.util.Pair;

// a simple cache for the results of the method <code>createList</code>
public final class IfFormulaInstantiationCache {
    
    private final LRUCache<Integer, Pair<Semisequent,ImmutableList<IfFormulaInstantiation>>> antecCache = new LRUCache<>(50);
    private final LRUCache<Integer, Pair<Semisequent,ImmutableList<IfFormulaInstantiation>>> succCache = new LRUCache<>(50);

    private final ReentrantReadWriteLock lock = new ReentrantReadWriteLock();
    private final ReadLock readLock = lock.readLock();
    private final WriteLock writeLock = lock.writeLock();
    
    public final ImmutableList<IfFormulaInstantiation> get(boolean antec, Semisequent s) {
        try {
            readLock.lock();
            final Pair<Semisequent,ImmutableList<IfFormulaInstantiation>> p = 
                    (antec ? antecCache : succCache).get(System.identityHashCode(s));
            return p != null && p.first == s ? p.second : null;
        } finally {
            readLock.unlock();
        }
    }

    public final void put(boolean antec, Semisequent s, ImmutableList<IfFormulaInstantiation> value) {
        try {
            writeLock.lock();
            (antec ? antecCache : succCache).put(System.identityHashCode(s), new Pair<>(s, value));
        } finally {
            writeLock.unlock();
        }
    }
}
