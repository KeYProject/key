/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.ldt;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.ast.abstraction.Type;
import de.uka.ilkd.key.java.ast.expression.Expression;
import de.uka.ilkd.key.java.ast.expression.Operator;
import de.uka.ilkd.key.java.ast.expression.literal.EmptySetLiteral;
import de.uka.ilkd.key.java.ast.expression.literal.Literal;
import de.uka.ilkd.key.java.ast.expression.operator.LogicFunctionalOperator;
import de.uka.ilkd.key.java.ast.reference.ExecutionContext;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermServices;

import org.key_project.logic.Name;
import org.key_project.logic.op.Function;
import org.key_project.util.ExtList;

import org.jspecify.annotations.Nullable;


public final class LocSetLDT extends LDT {

    public static final Name NAME = new Name("LocSet");
    public static final String INTERSECT_STRING = "intersect";
    public static final String SETMINUS_STRING = "setMinus";
    public static final String UNION_STRING = "union";

    private final Function empty;
    private final Function allLocs;
    private final Function singleton;
    private final Function union;
    private final Function intersect;
    private final Function setMinus;
    private final Function infiniteUnion;
    private final Function allFields;
    private final Function allObjects;
    private final Function arrayRange;
    private final Function freshLocs;
    private final Function elementOf;
    private final Function subset;
    private final Function disjoint;
    private final Function createdInHeap;


    public LocSetLDT(TermServices services) {
        super(NAME, services);
        empty = addFunction(services, "empty");
        allLocs = addFunction(services, "allLocs");
        singleton = addFunction(services, "singleton");
        union = addFunction(services, "union");
        intersect = addFunction(services, "intersect");
        setMinus = addFunction(services, "setMinus");
        infiniteUnion = addFunction(services, "infiniteUnion");
        allFields = addFunction(services, "allFields");
        allObjects = addFunction(services, "allObjects");
        arrayRange = addFunction(services, "arrayRange");
        freshLocs = addFunction(services, "freshLocs");
        elementOf = addFunction(services, "elementOf");
        subset = addFunction(services, "subset");
        disjoint = addFunction(services, "disjoint");
        createdInHeap = addFunction(services, "createdInHeap");
    }


    public Function getEmpty() {
        return empty;
    }


    public Function getAllLocs() {
        return allLocs;
    }


    public Function getSingleton() {
        return singleton;
    }


    public Function getUnion() {
        return union;
    }


    public Function getIntersect() {
        return intersect;
    }


    public Function getSetMinus() {
        return setMinus;
    }


    public Function getInfiniteUnion() {
        return infiniteUnion;
    }


    public Function getAllFields() {
        return allFields;
    }


    public Function getAllObjects() {
        return allObjects;
    }


    public Function getArrayRange() {
        return arrayRange;
    }


    public Function getFreshLocs() {
        return freshLocs;
    }


    public Function getElementOf() {
        return elementOf;
    }


    public Function getSubset() {
        return subset;
    }


    public Function getDisjoint() {
        return disjoint;
    }


    public Function getCreatedInHeap() {
        return createdInHeap;
    }


    @Override
    public boolean isResponsible(Operator op, JTerm[] subs,
            Services services, ExecutionContext ec) {
        return isResponsible(op, (JTerm) null, services, ec);
    }


    @Override
    public boolean isResponsible(Operator op, JTerm left, JTerm right,
            Services services, ExecutionContext ec) {
        return false;
    }


    @Override
    public boolean isResponsible(Operator op, JTerm sub,
            TermServices services, ExecutionContext ec) {
        if (op instanceof LogicFunctionalOperator lfo) {
            return lfo.getFunction().returnType == PrimitiveType.JAVA_LOCSET;
        }
        return false;
    }


    @Override
    public JTerm translateLiteral(Literal lit, Services services) {
        assert lit instanceof EmptySetLiteral;
        return services.getTermBuilder().func(empty);
    }


    @Override
    public Function getFunctionFor(Operator op, Services serv,
            ExecutionContext ec) {
        if (!(op instanceof LogicFunctionalOperator lfo)) {
            assert false;
            return null;
        }

        return switch (lfo.getFunction()) {
            case Singleton -> singleton;
            case SetUnion -> union;
            case Intersect -> intersect;
            case SetMinus -> setMinus;
            case AllFields -> allFields;
            default -> throw new IllegalStateException();
        };
    }

    @Override
    public boolean hasLiteralFunction(Function f) {
        return f.equals(empty);
    }


    @Override
    public Expression translateTerm(JTerm t, ExtList children, Services services) {
        if (t.op().equals(empty)) {
            return EmptySetLiteral.LOCSET;
        }
        assert false;
        return null;
    }


    @Override
    public Type getType(JTerm t) {
        assert false;
        return null;
    }

    @Override
    public @Nullable Function getFunctionFor(String operationName, Services services) {
        return switch (operationName) {
            case "add" -> getUnion();
            case "sub" -> getSetMinus();
            case "mul" -> getIntersect();
            case "le" -> getSubset();
            default -> null;
        };
    }
}
