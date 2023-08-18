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
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;

import org.key_project.util.ExtList;

public class PermissionLDT extends LDT {

    public static final Name NAME = new Name("Permission");

    private final Function permissionsFor;

    public PermissionLDT(Services services) {
        super(NAME, services);
        permissionsFor = addFunction(services, "permissionsFor");
    }

    public Function getPermissionsFor() {
        return permissionsFor;
    }

    @Override
    public boolean isResponsible(de.uka.ilkd.key.java.expression.Operator op, Term[] subs,
            Services services, ExecutionContext ec) {
        // TODO Auto-generated method stub
        return false;
    }

    public boolean isResponsible(de.uka.ilkd.key.java.expression.Operator op, Term left, Term right,
            Services services, ExecutionContext ec) {
        return false;
    }


    public boolean isResponsible(de.uka.ilkd.key.java.expression.Operator op, Term sub,
            de.uka.ilkd.key.logic.TermServices services, ExecutionContext ec) {
        return false;
    }

    @Override
    public Term translateLiteral(Literal lit, Services services) {
        assert false : "PermissionLDT: there are no permission literals: " + lit;
        return null;
    }

    @Override
    public Function getFunctionFor(Operator op, Services services, ExecutionContext ec) {
        assert false : "PermissionLDT: there are no permission operators: " + op;
        return null;
    }

    @Override
    public boolean hasLiteralFunction(Function f) {
        return false;
    }

    @Override
    public Expression translateTerm(Term t, ExtList children, Services services) {
        assert false : "PermissionLDT: Cannot convert term to program: " + t;
        return null;
    }

    @Override
    public Type getType(Term t) {
        assert false : "PermissionLDT: there are no types associated with permissions " + t;
        return null;
    }
}
