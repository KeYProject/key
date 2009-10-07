// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.visualdebugger.statevisualisation;

import java.util.*;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.ClassType;
import de.uka.ilkd.key.java.declaration.ArrayDeclaration;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Equality;

public class SymbolicArrayObject extends SymbolicObject {

    private HashMap equClass2Repr;

    private final HashMap index2post = new HashMap();

    private final HashMap index2SO = new HashMap();

    private final HashMap index2term = new HashMap();

    private ImmutableSet<Term> indexConfiguration;

    private HashMap indexTerm2EquClass;

    private LinkedList possibleIndexTermConfigurations;

    public SymbolicArrayObject(ImmutableSet<Term> cl, ClassType t, Services s) {
        super(cl, t, s);
        assert (t instanceof ArrayDeclaration);
    }

    public SymbolicArrayObject(Term cl, ClassType t, Services s,
            ImmutableSet<Term> possibleIndexTerms) {
        super(DefaultImmutableSet.<Term>nil().add(cl), t, s);
        // this.possibleIndexTerms=possibleIndexTerms;
    }

    public void addAssociationFromIndex(Term index, SymbolicObject so) {
        index2SO.put(index, so);
    }

    public void addIndexConstraint(Term g, Term o) {
        Term f = g;
        if (indexTerm2EquClass.containsKey(g)
                && this.equClass2Repr.containsKey(indexTerm2EquClass.get(g)))
            f = (Term) equClass2Repr.get(indexTerm2EquClass.get(g));

        if (index2term.containsKey(f)) {
            ImmutableList<Term> t = (ImmutableList<Term>) index2term.get(f);
            t = t.append(o);
            index2term.remove(f);
            index2term.put(f, t);

        } else {
            ImmutableList<Term> t = ImmutableSLList.<Term>nil().append(o);
            index2term.put(f, t);
        }

    }

    /**
     * return all index terms used in this array object figures
     */

    public ImmutableSet<Term> getAllIndexTerms() {
        ImmutableSet<Term> result = DefaultImmutableSet.<Term>nil();
        // System.out.println("PRIM "+this.isPrimitiveType());
        // System.out.println(index2term);
        // System.out.println(this.index2S0);
        HashSet s = new HashSet((this.isPrimitiveType()) ? index2term.keySet()
                : this.index2SO.keySet());
        HashSet val = new HashSet(this.equClass2Repr.values());
        s.addAll(val);

        for (Iterator it = s.iterator(); it.hasNext();) {
            result = result.add((Term) it.next());
        }
        return result;
    }

    public ImmutableSet<Term> getAllPostIndex() {
        ImmutableSet<Term> result = DefaultImmutableSet.<Term>nil();
        Set s = index2post.keySet();
        for (Iterator it = s.iterator(); it.hasNext();) {
            result = result.add((Term) it.next());
        }
        return result;
    }

    public SymbolicObject getAssociationEndForIndex(Term index) {
        // System.out.println("getIndex "+index2SO);
        return (SymbolicObject) index2SO.get(index);
    }

    public ImmutableList<Term> getConstraintsForIndex(Term index) {
        return (ImmutableList<Term>) index2term.get(index);
    }

    /**
     * return the index configuration
     * 
     * @return the SetOf<Term> representing the index config.
     */
    public ImmutableSet<Term> getIndexConfiguration() {
        return this.indexConfiguration;

    }

    public String getInstanceName() {
        // TODO
        return "Array_" + getId();
    }

    public LinkedList getPossibleIndexTermConfigurations() {
        return possibleIndexTermConfigurations;
    }

    // public getal

    /**
     * Finds a proper representantive for equivalence class cl.
     * 
     * @param cl
     */
    private Term getRepres(EquClass cl) {
        Term result = cl.getMembers().iterator().next();
        for (Iterator<Term> it = cl.getMembers().iterator(); it.hasNext();) {
            Term next = it.next();
            if (isNumberLiteral(next)) {
                result = next;
            }
        }

        return result;
    }

    public Term getValueTermForIndex(Term index) {
        return (Term) this.index2post.get(index);
    }

    private boolean isNumberLiteral(Term t) {
        char c = t.toString().charAt(0);
        return c == 'Z';
    }

    public boolean isPrimitiveType() {
        return !(((ArrayDeclaration) getType()).getBaseType().getKeYJavaType()
                .getJavaType() instanceof ClassType);
    }

    /**
     * sets the index configuration
     * 
     * @param constraints
     */
    public void setIndexConfiguration(ImmutableSet<Term> constraints) {
        indexTerm2EquClass = new HashMap();
        // s.i
        Iterator<Term> it = constraints.iterator();
        while (it.hasNext()) {
            EquClass ec = null;
            Term t = it.next();
            if (t.op() instanceof Equality /* && !containsImplicitAttr(t) */) {
                if (indexTerm2EquClass.containsKey(t.sub(0))) {
                    ec = (EquClass) indexTerm2EquClass.get(t.sub(0));
                    if (indexTerm2EquClass.containsKey(t.sub(1))) {
                        ec.add((EquClass) indexTerm2EquClass.get(t.sub(1)));
                    } else {
                        ec.add(t.sub(1));
                    }
                } else if (indexTerm2EquClass.containsKey(t.sub(1))) {
                    ec = (EquClass) indexTerm2EquClass.get(t.sub(1));
                    ec.add(t.sub(0));
                } else {
                    ec = new EquClass(t.sub(0), t.sub(1));
                }
                Iterator<Term> ecIt = ec.getMembers().iterator();
                while (ecIt.hasNext()) {
                    indexTerm2EquClass.put(ecIt.next(), ec);
                }
            } else {
                if (!indexTerm2EquClass.containsKey(t.sub(0).sub(1))) {
                    ec = new EquClass(t.sub(0).sub(1));
                    indexTerm2EquClass.put(t.sub(0).sub(1), ec);
                }
                if (!indexTerm2EquClass.containsKey(t.sub(0).sub(0))) {
                    ec = new EquClass(t.sub(0).sub(0));
                    indexTerm2EquClass.put(t.sub(0).sub(0), ec);
                }

            }

        }

        this.equClass2Repr = new HashMap();
        for (Iterator it2 = this.indexTerm2EquClass.values().iterator(); it2
                .hasNext();) {

            EquClass cl = (EquClass) it2.next();
            this.equClass2Repr.put(cl, getRepres(cl));
            /*
             * System.out.println("AAAAAAAAAAA"); System.out.println("Class
             * "+cl.members ); System.out.println("Repr "+this.getRepres(cl));
             */}

        this.indexConfiguration = constraints;

    }

    /**
     * sets all possible index configurations
     * 
     * @param possibleIndexTerms
     */
    public void setPossibleIndexTermConfigurations(LinkedList possibleIndexTerms) {
        this.possibleIndexTermConfigurations = possibleIndexTerms;
    }

    public void setValueTermForIndex(Term index, Term value) {
        Term f = index;
        if (indexTerm2EquClass.containsKey(index)
                && this.equClass2Repr
                        .containsKey(indexTerm2EquClass.get(index)))
            f = (Term) equClass2Repr.get(indexTerm2EquClass.get(index));

        this.index2post.put(f, value);
    }

    private class EquClass {
        private ImmutableSet<Term> disjointRep = DefaultImmutableSet.<Term>nil();

        private ImmutableSet<Term> members;

        public EquClass(ImmutableSet<Term> members) {
            this.members = members;

        }

        public EquClass(Term t) {
            this(DefaultImmutableSet.<Term>nil().add(t));
        }

        public EquClass(Term t1, Term t2) {
            this(DefaultImmutableSet.<Term>nil().add(t1).add(t2));
        }

        public void add(EquClass ec) {
            members = members.union(ec.getMembers());
        }

        public void add(Term t) {
            members = members.add(t);
        }

        public void addDisjoint(Term t) {
            disjointRep = disjointRep.add(t);
        }

        public ImmutableSet<Term> getDisjoints() {
            return disjointRep;
        }

        public ImmutableSet<Term> getMembers() {
            return members;
        }

        public String toString() {
            return "EquClass: (" + members + ")  Disjoint + "
                    + this.disjointRep + " /";
        }

    }

}
