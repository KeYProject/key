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

    private final ParametricFunctionDecl empty;
    private final ParametricFunctionDecl singleton;
    private final ParametricFunctionDecl union;
    private final ParametricFunctionDecl intersect;
    private final ParametricFunctionDecl setMinus;
    private final ParametricFunctionDecl infiniteUnion;
    private final ParametricFunctionDecl card;
    private final ParametricFunctionDecl elementOf;
    private final ParametricFunctionDecl subset;
    private final ParametricFunctionDecl disjoint;


    public SetLDT(TermServices services) {
        super(NAME, services);

        empty = addParametricFunction(services, "empty");
        singleton = addParametricFunction(services, "singleton");
        union = addParametricFunction(services, "union");
        intersect = addParametricFunction(services, "intersect");
        setMinus = addParametricFunction(services, "setMinus");
        infiniteUnion = addParametricFunction(services, "infiniteUnion");
        card = addParametricFunction(services, "sCard");
        elementOf = addParametricFunction(services, "elementOf");
        subset = addParametricFunction(services, "subset");
        disjoint = addParametricFunction(services, "disjoint");
    }

    public ParametricFunctionDecl getEmpty() {
        return empty;
    }

    public ParametricFunctionDecl getSingleton() {
        return singleton;
    }

    public ParametricFunctionDecl getUnion() {
        return union;
    }

    public ParametricFunctionDecl getIntersect() {
        return intersect;
    }

    public ParametricFunctionDecl getSetMinus() {
        return setMinus;
    }

    public ParametricFunctionDecl getInfiniteUnion() {
        return infiniteUnion;
    }

    public ParametricFunctionDecl getCard() {
        return card;
    }

    public ParametricFunctionDecl getElementOf() {
        return elementOf;
    }

    public ParametricFunctionDecl getSubset() {
        return subset;
    }

    public ParametricFunctionDecl getDisjoint() {
        return disjoint;
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
