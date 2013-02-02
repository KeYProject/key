// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 


package de.uka.ilkd.key.smt;

import java.util.Iterator;
import java.util.LinkedList;

/**
 * Stores a set of solver types. This class can be used in order to encapsulate multiple solvers.
 */
public class SolverTypeCollection implements Iterable<SolverType> {
    public final static SolverTypeCollection EMPTY_COLLECTION = new SolverTypeCollection();

    private LinkedList<SolverType> types = new LinkedList<SolverType>();
    private String name = "";
    private int minUsableSolver = 1;

    private int hashCode = -1;

    /**
     * 
     * @param type
     *            at least on solver type must be passed.
     * @param types
     * @param minUsableSolvers
     *            specifies how many solvers at leas must be usable, so that
     *            <code>isUsable</code> returns true.
     */
    public SolverTypeCollection(String name, int minUsableSolvers,
	    SolverType type, SolverType... types) {
	this.types.add(type);
	this.name = name;
	this.minUsableSolver = minUsableSolvers;
	for (SolverType t : types) {
	    this.types.add(t);
	}
    }

    public SolverTypeCollection(String[] solverNames) {

    }

    private SolverTypeCollection() {

    }

    public boolean equals(Object o) {
        if (!(o instanceof SolverTypeCollection)) {
            return false;
        }
        SolverTypeCollection stc = (SolverTypeCollection) o;
        return name.equals(stc.name) && minUsableSolver == stc.minUsableSolver && types.equals(stc.types);
    }

    public int hashCode() {
        if (hashCode == -1) {
            hashCode = (minUsableSolver + 1) * name.hashCode();
            for (SolverType type:types) {
                hashCode = hashCode + 7*type.hashCode();
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
		String s = "";

		int i = 0;
		for (SolverType type : types) {
			if (type.isInstalled(false)) {
				if (i > 0) {
					s += ", ";
				}
				s += type.getName();
				i++;
			}
		}
		if (s.isEmpty()) {
			return "No solver available.";
		}
		return s;
	}

	@Override
	public Iterator<SolverType> iterator() {
		return types.iterator();
	}
}
