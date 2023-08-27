/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof;


/** Proof-specific counter object: taclet names, var names, node numbers, &c */
public class Counter {

    private final String name;
    private int count;

    public Counter(String name) {
        this.name = name;
    }

    private Counter(String name, int count) {
        this(name);
        this.count = count;
    }

    public int getCount() {
        return count;
    }

    public int getCountPlusPlus() {
        return count++;
    }

    public String toString() {
        return "Counter " + name + ": " + count;
    }

    public Counter copy() {
        return new Counter(name, count);
    }
}
