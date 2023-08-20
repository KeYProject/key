/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.smt;

import java.util.Collection;
import java.util.Collections;
import java.util.Iterator;
import java.util.LinkedList;

import de.uka.ilkd.key.smt.solvertypes.SolverType;

/**
 * Stores a set of solver types. This class can be used in order to encapsulate multiple solvers.
 */
public class SolverTypeCollection implements Iterable<SolverType> {
    public final static SolverTypeCollection EMPTY_COLLECTION = new SolverTypeCollection();

    private final LinkedList<SolverType> types = new LinkedList<>();
    private String name = "";
    private int minUsableSolver = 1;

    private int hashCode = -1;

    /**
     *
     * @param type at least on solver type must be passed.
     * @param types
     * @param minUsableSolvers specifies how many solvers at leas must be usable, so that
     *        <code>isUsable</code> returns true.
     */
    public SolverTypeCollection(String name, int minUsableSolvers, SolverType type,
            SolverType... types) {
        this.types.add(type);
        this.name = name;
        this.minUsableSolver = minUsableSolvers;
        Collections.addAll(this.types, types);
    }

    /**
     * Instantiates a new solver type collection.
     *
     * @param name the name of the solver
     * @param minUsableSolvers the min number of usable solvers
     * @param types the types to add
     */
    public SolverTypeCollection(String name, int minUsableSolvers, Collection<SolverType> types) {
        this.name = name;
        this.minUsableSolver = minUsableSolvers;
        this.types.addAll(types);
    }

    private SolverTypeCollection() {

    }

    public boolean equals(Object o) {
        if (!(o instanceof SolverTypeCollection)) {
            return false;
        }
        SolverTypeCollection stc = (SolverTypeCollection) o;
        return name.equals(stc.name) && minUsableSolver == stc.minUsableSolver
                && types.equals(stc.types);
    }

    public int hashCode() {
        if (hashCode == -1) {
            hashCode = (minUsableSolver + 1) * name.hashCode();
            for (SolverType type : types) {
                hashCode = hashCode + 7 * type.hashCode();
            }
            if (hashCode == -1) {
                hashCode = 0;
            }
        }
        return hashCode;
    }

    public LinkedList<SolverType> getTypes() {
        return types;
    }

    public boolean isUsable() {
        int usableCount = 0;
        for (SolverType type : types) {
            if (type.isInstalled(false)) {
                usableCount++;
            }
        }

        return usableCount >= minUsableSolver;
    }

    public String name() {
        return name;
    }

    public String toString() {
        StringBuilder s = new StringBuilder();

        int i = 0;
        for (SolverType type : types) {
            if (type.isInstalled(false)) {
                if (i > 0) {
                    s.append(", ");
                }
                s.append(type.getName());
                i++;
            }
        }
        if (s.length() == 0) {
            return "No solver available.";
        }
        return s.toString();
    }

    @Override
    public Iterator<SolverType> iterator() {
        return types.iterator();
    }
}
