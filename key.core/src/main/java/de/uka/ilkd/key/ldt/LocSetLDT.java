/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.ldt;

import java.util.List;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.abstraction.Type;
import de.uka.ilkd.key.java.ast.expression.Expression;
import de.uka.ilkd.key.java.ast.expression.Operator;
import de.uka.ilkd.key.java.ast.expression.literal.EmptySetLiteral;
import de.uka.ilkd.key.java.ast.expression.literal.Literal;
import de.uka.ilkd.key.java.ast.expression.operator.LogicFunctionalOperator;
import de.uka.ilkd.key.java.ast.reference.ExecutionContext;
import de.uka.ilkd.key.logic.GenericArgument;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.ParametricFunctionInstance;

import org.key_project.logic.Name;
import org.key_project.logic.op.Function;
import org.key_project.util.ExtList;
import org.key_project.util.collection.ImmutableList;

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
    private final Function pair;


    public LocSetLDT(Services services) {
        super(NAME, services);
        empty = getInstantiatedFunction("empty", services);
        allLocs = addFunction(services, "allLocs");
        singleton = getInstantiatedFunction("singleton", services);
        union = getInstantiatedFunction("union", services);
        intersect = getInstantiatedFunction("intersect", services);
        setMinus = getInstantiatedFunction("setMinus", services);
        infiniteUnion = getInstantiatedFunction("infiniteUnion", services);
        allFields = addFunction(services, "allFields");
        allObjects = addFunction(services, "allObjects");
        arrayRange = addFunction(services, "arrayRange");
        freshLocs = addFunction(services, "freshLocs");
        elementOf = getInstantiatedFunction("elementOf", services);
        subset = getInstantiatedFunction("subset", services);
        disjoint = getInstantiatedFunction("disjoint", services);
        createdInHeap = addFunction(services, "createdInHeap");
        pair = getInstantiatedFunction("pair", services, ImmutableList.fromList(List.of(
            new GenericArgument(services.getNamespaces().sorts().lookup("java.lang.Object")),
            new GenericArgument(services.getNamespaces().sorts().lookup("Field")))));
    }

    private Function getInstantiatedFunction(String name, Services services,
            ImmutableList<GenericArgument> args) {
        return ParametricFunctionInstance.get(addParametricFunction(services, name), args,
            services);
    }

    private Function getInstantiatedFunction(String name, Services services) {
        return getInstantiatedFunction(
            name,
            services,
            ImmutableList.fromList(List.of(
                new GenericArgument(
                    services.getNamespaces().sortAliases().lookup("Loc").aliasedSort()))));
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

    public Function getPair() {
        return pair;
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
            // getFunctionFor does not support all loc set functions, e.g. array range etc.
            // return lfo.getFunction().returnType == PrimitiveType.JAVA_LOCSET;
            return switch (lfo.getFunction()) {
                case Singleton, SetUnion, Intersect,
                        SetMinus, AllFields, AllObjects ->
                    true;
                default -> false;
            };
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
            case AllObjects -> allObjects;
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
