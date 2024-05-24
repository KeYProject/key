/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.ldt;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.java.expression.literal.EmptySetLiteral;
import de.uka.ilkd.key.java.expression.operator.Intersect;
import de.uka.ilkd.key.java.expression.operator.adt.AllFields;
import de.uka.ilkd.key.java.expression.operator.adt.SetMinus;
import de.uka.ilkd.key.java.expression.operator.adt.SetUnion;
import de.uka.ilkd.key.java.expression.operator.adt.Singleton;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.JFunction;

import org.key_project.logic.Name;
import org.key_project.util.ExtList;

import org.jspecify.annotations.Nullable;


public final class LocSetLDT extends LDT {

    public static final Name NAME = new Name("LocSet");

    private final JFunction empty;
    private final JFunction allLocs;
    private final JFunction singleton;
    private final JFunction union;
    private final JFunction intersect;
    private final JFunction setMinus;
    private final JFunction infiniteUnion;
    private final JFunction allFields;
    private final JFunction allObjects;
    private final JFunction arrayRange;
    private final JFunction freshLocs;
    private final JFunction elementOf;
    private final JFunction subset;
    private final JFunction disjoint;
    private final JFunction createdInHeap;


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


    public JFunction getEmpty() {
        return empty;
    }


    public JFunction getAllLocs() {
        return allLocs;
    }


    public JFunction getSingleton() {
        return singleton;
    }


    public JFunction getUnion() {
        return union;
    }


    public JFunction getIntersect() {
        return intersect;
    }


    public JFunction getSetMinus() {
        return setMinus;
    }


    public JFunction getInfiniteUnion() {
        return infiniteUnion;
    }


    public JFunction getAllFields() {
        return allFields;
    }


    public JFunction getAllObjects() {
        return allObjects;
    }


    public JFunction getArrayRange() {
        return arrayRange;
    }


    public JFunction getFreshLocs() {
        return freshLocs;
    }


    public JFunction getElementOf() {
        return elementOf;
    }


    public JFunction getSubset() {
        return subset;
    }


    public JFunction getDisjoint() {
        return disjoint;
    }


    public JFunction getCreatedInHeap() {
        return createdInHeap;
    }


    @Override
    public boolean isResponsible(de.uka.ilkd.key.java.expression.Operator op, Term[] subs,
            Services services, ExecutionContext ec) {
        return isResponsible(op, (Term) null, services, ec);
    }


    @Override
    public boolean isResponsible(de.uka.ilkd.key.java.expression.Operator op, Term left, Term right,
            Services services, ExecutionContext ec) {
        return false;
    }


    @Override
    public boolean isResponsible(de.uka.ilkd.key.java.expression.Operator op, Term sub,
            TermServices services, ExecutionContext ec) {
        return op instanceof Singleton || op instanceof SetUnion || op instanceof Intersect
                || op instanceof SetMinus || op instanceof AllFields;
    }


    @Override
    public Term translateLiteral(Literal lit, Services services) {
        assert lit instanceof EmptySetLiteral;
        return services.getTermBuilder().func(empty);
    }


    @Override
    public JFunction getFunctionFor(de.uka.ilkd.key.java.expression.Operator op, Services serv,
            ExecutionContext ec) {
        if (op instanceof Singleton) {
            return singleton;
        } else if (op instanceof SetUnion) {
            return union;
        } else if (op instanceof Intersect) {
            return intersect;
        } else if (op instanceof SetMinus) {
            return setMinus;
        } else if (op instanceof AllFields) {
            return allFields;
        }
        assert false;
        return null;
    }


    @Override
    public boolean hasLiteralFunction(JFunction f) {
        return f.equals(empty);
    }


    @Override
    public Expression translateTerm(Term t, ExtList children, Services services) {
        if (t.op().equals(empty)) {
            return EmptySetLiteral.LOCSET;
        }
        assert false;
        return null;
    }


    @Override
    public Type getType(Term t) {
        assert false;
        return null;
    }

    @Override
    public @Nullable JFunction getFunctionFor(String operationName, Services services) {
        return switch (operationName) {
        case "add" -> getUnion();
        case "sub" -> getSetMinus();
        case "mul" -> getIntersect();
        case "le" -> getSubset();
        default -> null;
        };
    }
}
