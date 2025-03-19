/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule;

import java.util.concurrent.locks.ReentrantReadWriteLock;
import java.util.concurrent.locks.ReentrantReadWriteLock.ReadLock;
import java.util.concurrent.locks.ReentrantReadWriteLock.WriteLock;

import de.uka.ilkd.key.logic.Semisequent;

import org.key_project.util.LRUCache;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.Pair;

// a simple cache for the results of the method <code>createList</code>
public final class IfFormulaInstantiationCache {

    private final LRUCache<Integer, Pair<Semisequent, ImmutableArray<IfFormulaInstantiation>>> antecCache =
        new LRUCache<>(50);
    private final LRUCache<Integer, Pair<Semisequent, ImmutableArray<IfFormulaInstantiation>>> succCache =
        new LRUCache<>(50);

    private final ReentrantReadWriteLock lock = new ReentrantReadWriteLock();
    private final ReadLock readLock = lock.readLock();
    private final WriteLock writeLock = lock.writeLock();

    public ImmutableArray<IfFormulaInstantiation> get(boolean antec, Semisequent s) {
        try {
            readLock.lock();
            final Pair<Semisequent, ImmutableArray<IfFormulaInstantiation>> p =
                (antec ? antecCache : succCache).get(System.identityHashCode(s));
            return p != null && p.first == s ? p.second : null;
        } finally {
            readLock.unlock();
        }
    }

    public void put(boolean antec, Semisequent s,
            ImmutableArray<IfFormulaInstantiation> value) {
        try {
            writeLock.lock();
            (antec ? antecCache : succCache).put(System.identityHashCode(s), new Pair<>(s, value));
        } finally {
            writeLock.unlock();
        }
    }
}
