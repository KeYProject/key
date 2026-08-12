/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.ldt;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.expression.Expression;
import de.uka.ilkd.key.java.ast.expression.Operator;
import de.uka.ilkd.key.java.ast.expression.literal.Literal;
import de.uka.ilkd.key.java.ast.reference.ExecutionContext;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.ParametricFunctionDecl;

import org.key_project.logic.Name;
import org.key_project.logic.op.Function;
import org.key_project.util.ExtList;

import org.jspecify.annotations.Nullable;

public final class SetLDT extends ParametricLDT {
    public static final Name NAME = new Name("Set");

    private final ParametricFunctionDecl sEmpty;
    private final ParametricFunctionDecl sSingleton;
    private final ParametricFunctionDecl sUnion;
    private final ParametricFunctionDecl sIntersect;
    private final ParametricFunctionDecl sSetMinus;
    private final ParametricFunctionDecl sInfiniteUnion;
    private final ParametricFunctionDecl sCard;


    public SetLDT(TermServices services) {
        super(NAME, services);

        sEmpty = addParametricFunction(services, "sEmpty");
        sSingleton = addParametricFunction(services, "sSingleton");
        sUnion = addParametricFunction(services, "sUnion");
        sIntersect = addParametricFunction(services, "sIntersect");
        sSetMinus = addParametricFunction(services, "sSetMinus");
        sInfiniteUnion = addParametricFunction(services, "sInfiniteUnion");
        sCard = addParametricFunction(services, "sCard");
    }

    @Override
    public boolean isResponsible(Operator op, JTerm[] subs, Services services,
            ExecutionContext ec) {
        return false;
    }

    @Override
    public boolean isResponsible(Operator op, JTerm left, JTerm right, Services services,
            ExecutionContext ec) {
        return false;
    }

    @Override
    public boolean isResponsible(Operator op, JTerm sub, TermServices services,
            ExecutionContext ec) {
        return false;
    }

    @Override
    public JTerm translateLiteral(Literal lit, Services services) {
        return null;
    }

    @Override
    public @Nullable Function getFunctionFor(Operator op, Services services, ExecutionContext ec) {
        return null;
    }

    @Override
    public boolean hasLiteralFunction(Function f) {
        return false;
    }

    @Override
    public Expression translateTerm(JTerm t, ExtList children, Services services) {
        return null;
    }
}
