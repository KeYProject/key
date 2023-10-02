/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.ldt;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.java.expression.Operator;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.sort.Sort;

import org.key_project.logic.Name;
import org.key_project.util.ExtList;

public class JavaDLTheory extends LDT {

    protected JavaDLTheory(Name name, TermServices services) {
        super(name, services);
    }

    protected JavaDLTheory(Name name, Sort targetSort, TermServices services) {
        super(name, targetSort, services);
    }



    @Override
    public boolean isResponsible(Operator op, Term[] subs, Services services, ExecutionContext ec) {
        assert false;
        return false;
    }

    @Override
    public boolean isResponsible(Operator op, Term left, Term right, Services services,
            ExecutionContext ec) {
        assert false;
        return false;
    }

    @Override
    public boolean isResponsible(Operator op, Term sub, TermServices services,
            ExecutionContext ec) {
        assert false;
        return false;
    }

    @Override
    public Term translateLiteral(Literal lit, Services services) {
        assert false;
        return null;
    }

    @Override
    public Function getFunctionFor(Operator op, Services services, ExecutionContext ec) {
        assert false;
        return null;
    }

    @Override
    public boolean hasLiteralFunction(Function f) {
        assert false;
        return false;
    }

    @Override
    public Expression translateTerm(Term t, ExtList children, Services services) {
        assert false;
        return null;
    }

    @Override
    public Type getType(Term t) {
        assert false;
        return null;
    }
}
