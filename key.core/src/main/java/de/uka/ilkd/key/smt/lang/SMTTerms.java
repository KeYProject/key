/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.smt.lang;

import java.util.LinkedList;
import java.util.List;

/**
 *
 *
 * @author Aboubakr Achraf El Ghazi
 *
 */
public class SMTTerms extends SMTTerm {

    protected List<SMTTerm> terms;

    public SMTTerms(List<SMTTerm> terms) {
        this.terms = terms;
    }

    public List<SMTTerm> flatten() {
        List<SMTTerm> termList = new LinkedList<>();
        for (SMTTerm arg : this.getTerms()) {
            if (arg instanceof SMTTerms terms) {
                termList.addAll(terms.flatten());

            }
            termList.add(arg);
        }
        return termList;
    }

    /**
     * @return the terms
     */
    public List<SMTTerm> getTerms() {
        return terms;
    }

    /**
     * @param terms the terms to set
     */
    public void setTerms(List<SMTTerm> terms) {
        this.terms = terms;
    }

    /** {@inheritDoc} */
    @Override
    public SMTSort sort() {
        throw new RuntimeException(
            "Unexpected: Sort of a term list. The Method <sort()> don't support instances of <Terms>");
    }

    /*
     * (non-Javadoc)
     *
     * @see edu.kit.asa.alloy2smt.smt.Term#occurs(edu.kit.asa.alloy2smt.smt.TermVariable)
     */
    @Override
    public boolean occurs(SMTTermVariable a) {
        boolean b = false;
        for (SMTTerm term : terms) {
            b = b && term.occurs(a);
        }
        return b;
    }

    /*
     * (non-Javadoc)
     *
     * @see edu.kit.asa.alloy2smt.smt.Term#occurs(java.lang.String)
     */
    @Override
    public boolean occurs(String id) {
        for (SMTTerm term : terms) {
            if (term.occurs(id)) {
                return true;
            }
        }
        return false;
    }

    /*
     * (non-Javadoc)
     *
     * @see edu.kit.asa.alloy2smt.smt.Term#substitute(edu.kit.asa.alloy2smt.smt.TermVariable,
     * edu.kit.asa.alloy2smt.smt.Term)
     */
    @Override
    public SMTTerm substitute(SMTTermVariable a, SMTTerm b) {
        List<SMTTerm> ret = new LinkedList<>();
        for (SMTTerm term : terms) {
            ret.add(term.substitute(a, b));
        }
        return new SMTTerms(ret);
    }

    @Override
    public SMTTerm substitute(SMTTerm a, SMTTerm b) {
        List<SMTTerm> ret = new LinkedList<>();
        for (SMTTerm term : terms) {
            ret.add(term.substitute(a, b));
        }
        return new SMTTerms(ret);
    }

    @Override
    public SMTTerm replace(SMTTermCall a, SMTTerm b) {
        List<SMTTerm> ret = new LinkedList<>();
        for (SMTTerm term : terms) {
            ret.add(term.replace(a, b));
        }
        return new SMTTerms(ret);
    }

    @Override
    public SMTTerm instantiate(SMTTermVariable a, SMTTerm b) {
        List<SMTTerm> ret = new LinkedList<>();
        for (SMTTerm term : terms) {
            ret.add(term.instantiate(a, b));
        }
        return new SMTTerms(ret);
    }

    @Override
    public SMTTerms copy() {
        return new SMTTerms(this.terms);
    }

    public void add(SMTTerm t) {
        terms.add(t);
    }

    public String toString() {
        return this.toString(0);
    }

    public String toString(int nestPos) {
        StringBuilder ret = new StringBuilder();
        for (int i = 0; i < nestPos; i++) {
            ret.append(" ");
        }

        if (terms.size() == 0) {
            throw new RuntimeException("Unexpected: Empty args for TermLogicalOp ");
        }

        for (SMTTerm term : terms) {
            ret.append(term.toString(nestPos));
            ret.append(", ");
        }
        return ret.toString();
    }

}
