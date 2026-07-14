/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.ldt;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.abstraction.Type;
import de.uka.ilkd.key.java.ast.expression.Expression;
import de.uka.ilkd.key.java.ast.expression.Operator;
import de.uka.ilkd.key.java.ast.expression.literal.Literal;
import de.uka.ilkd.key.java.ast.expression.operator.Subtype;
import de.uka.ilkd.key.java.ast.reference.ExecutionContext;
import de.uka.ilkd.key.logic.GenericArgument;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.ParametricFunctionDecl;
import de.uka.ilkd.key.logic.op.ParametricFunctionInstance;
import de.uka.ilkd.key.proof.io.ProofSaver;

import org.key_project.logic.Name;
import org.key_project.logic.op.Function;
import org.key_project.logic.sort.Sort;
import org.key_project.util.ExtList;
import org.key_project.util.collection.ImmutableList;


public final class SortLDT extends LDT {

    public static final Name NAME = new Name("SORT");

    private final ParametricFunctionDecl ssort;
    private final Function ssubsort;

    public SortLDT(TermServices services) {
        super(NAME, services);
        ssort = addParametricFunction((Services) services, "ssort");
        ssubsort = addFunction(services, "ssubsort");
    }

    public ParametricFunctionInstance getSsort(Sort instanceSort, TermServices services) {
        return ParametricFunctionInstance.get(ssort,
            ImmutableList.of(new GenericArgument(instanceSort)), (Services) services);
    }

    public Function getSsubsort() {
        return ssubsort;
    }

    @Override
    public boolean isResponsible(Operator op, JTerm[] subs,
            Services services,
            ExecutionContext ec) {
        return op instanceof Subtype;
    }

    @Override
    public boolean isResponsible(Operator op, JTerm left, JTerm right,
            Services services,
            ExecutionContext ec) {
        return op instanceof Subtype;
    }

    @Override
    public boolean isResponsible(Operator op, JTerm sub,
            TermServices services,
            ExecutionContext ec) {
        return op instanceof Subtype;
    }

    @Override
    public JTerm translateLiteral(Literal lit, Services services) {
        assert false;
        return null;
    }

    @Override
    public Function getFunctionFor(Operator op, Services services,
            ExecutionContext ec) {
        if (op instanceof Subtype) {
            return ssubsort;
        }

        assert false;
        return null;
    }

    @Override
    public boolean hasLiteralFunction(Function f) {
        return f instanceof ParametricFunctionInstance sf && sf.getBase() == ssort;
    }

    @Override
    public Expression translateTerm(JTerm t, ExtList children, Services services) {
        if (t.op() instanceof ParametricFunctionInstance sf && sf.getBase() == ssort) {
            // TODO
        }

        throw new IllegalArgumentException(
            "Could not translate " + ProofSaver.printTerm(t, null) + " to program.");
    }

    @Override
    public Type getType(JTerm t) {
        assert false;
        return null;
    }
}
