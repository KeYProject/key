/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.ldt;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.java.expression.Operator;
import de.uka.ilkd.key.java.expression.literal.FreeLiteral;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermServices;

import org.key_project.logic.Name;
import org.key_project.logic.op.Function;
import org.key_project.util.ExtList;

/**
 * Generic data type, which has no predefined theory. It is meant as a basis to implement an
 * additional abstract data type, e.g., binary trees, stacks, etc. in <code>.key</code> files.
 *
 * @author Daniel Grahl
 *
 */
public final class FreeLDT extends LDT {

    public static final Name NAME = new Name("Free");

    // neutral element, the only pre-defined function
    private final Function atom;

    public FreeLDT(TermServices services) {
        super(NAME, services);
        atom = addFunction(services, "atom");
    }

    @Override
    public boolean isResponsible(Operator op, JTerm[] subs, Services services,
            ExecutionContext ec) {
        // TODO Auto-generated method stub
        return false;
    }

    @Override
    public boolean isResponsible(Operator op, JTerm left, JTerm right, Services services,
            ExecutionContext ec) {
        // TODO Auto-generated method stub
        return false;
    }

    @Override
    public boolean isResponsible(Operator op, JTerm sub, TermServices services,
            ExecutionContext ec) {
        // TODO Auto-generated method stub
        return false;
    }

    @Override
    public JTerm translateLiteral(Literal lit, Services services) {
        return services.getTermBuilder().func(atom);
    }

    @Override
    public Function getFunctionFor(Operator op, Services services, ExecutionContext ec) {
        // TODO Auto-generated method stub
        assert false;
        return null;
    }

    @Override
    public boolean hasLiteralFunction(Function f) {
        return "atom".equals(f.name().toString());
    }

    @Override
    public Expression translateTerm(JTerm t, ExtList children, Services services) {
        if (t.op() instanceof Function && hasLiteralFunction((Function) t.op())) {
            return FreeLiteral.INSTANCE;
        }
        assert false;
        return null;
    }

    @Override
    public Type getType(JTerm t) {
        assert false;
        return null;
    }

    public Function getAtom() {
        return atom;
    }

}
