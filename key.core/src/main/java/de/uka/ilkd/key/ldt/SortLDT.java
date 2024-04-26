/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.ldt;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.java.expression.Operator;
import de.uka.ilkd.key.java.expression.operator.Subtype;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.JFunction;
import de.uka.ilkd.key.logic.op.SortDependingFunction;
import de.uka.ilkd.key.proof.io.ProofSaver;

import org.key_project.logic.Name;
import org.key_project.logic.sort.Sort;
import org.key_project.util.ExtList;


public final class SortLDT extends LDT {

    public static final Name NAME = new Name("SORT");

    private final SortDependingFunction ssort;
    private final JFunction ssubsort;

    public SortLDT(TermServices services) {
        super(NAME, services);
        ssort = addSortDependingFunction(services, "ssort");
        ssubsort = addFunction(services, "ssubsort");
    }

    public SortDependingFunction getSsort(Sort instanceSort, TermServices services) {
        return ssort.getInstanceFor(instanceSort, services);
    }

    public JFunction getSsubsort() {
        return ssubsort;
    }

    @Override
    public boolean isResponsible(Operator op, Term[] subs, Services services, ExecutionContext ec) {
        return op instanceof Subtype;
    }

    @Override
    public boolean isResponsible(Operator op, Term left, Term right, Services services,
            ExecutionContext ec) {
        return op instanceof Subtype;
    }

    @Override
    public boolean isResponsible(Operator op, Term sub, TermServices services,
            ExecutionContext ec) {
        return op instanceof Subtype;
    }

    @Override
    public Term translateLiteral(Literal lit, Services services) {
        assert false;
        return null;
    }

    @Override
    public JFunction getFunctionFor(Operator op, Services services, ExecutionContext ec) {
        if (op instanceof Subtype) {
            return ssubsort;
        }

        assert false;
        return null;
    }

    @Override
    public boolean hasLiteralFunction(JFunction f) {
        return f instanceof SortDependingFunction sf && sf.isSimilar(ssort);
    }

    @Override
    public Expression translateTerm(Term t, ExtList children, Services services) {
        if (t.op() instanceof SortDependingFunction sf && sf.isSimilar(ssort)) {
            // TODO
        }

        throw new IllegalArgumentException(
            "Could not translate " + ProofSaver.printTerm(t, null) + " to program.");
    }

    @Override
    public Type getType(Term t) {
        assert false;
        return null;
    }
}
