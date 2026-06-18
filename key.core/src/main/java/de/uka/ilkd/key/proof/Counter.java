/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof;


import java.util.concurrent.atomic.AtomicInteger;

/**
 * Proof-specific counter object: taclet names, var names, node numbers, etc.
 *
 * <p>
 * A single {@link de.uka.ilkd.key.java.Services} (and thus its counters) is shared by all goals of
 * a proof. To make counter-based fresh-name minting safe once goals are processed on worker threads
 * (multithreading effort, branch {@code bubel/mt-goals}), the increment is atomic. This is
 * behaviour-preserving for single-threaded use: {@link #getCountPlusPlus()} still returns the
 * pre-increment value and {@link #copy()} still snapshots the current value.
 */
public class Counter {

    private final String name;
    private final AtomicInteger count;

    public Counter(String name) {
        this(name, 0);
    }

    private Counter(String name, int count) {
        this.name = name;
        this.count = new AtomicInteger(count);
    }

    public int getCount() {
        return count.get();
    }

    public int getCountPlusPlus() {
        return count.getAndIncrement();
    }

    public String toString() {
        return "Counter " + name + ": " + count.get();
    }

    public Counter copy() {
        return new Counter(name, count.get());
    }
}
