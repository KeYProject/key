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
import de.uka.ilkd.key.logic.op.JFunction;
import de.uka.ilkd.key.logic.op.SortDependingFunction;
import de.uka.ilkd.key.logic.sort.SortImpl;

import org.key_project.logic.Name;
import org.key_project.logic.sort.Sort;
import org.key_project.util.ExtList;

/**
 * The JavaDL theory class provides access to function symvols, sorts that are part of the core
 * logic
 * like cast or instanceof functions.
 */
public class JavaDLTheory extends LDT {

    /**
     * Name of {@link #getExactInstanceofSymbol(Sort,TermServices)}.
     */
    public static final Name EXACT_INSTANCE_NAME = new Name("exactInstance");
    /**
     * Name of {@link #getCastSymbol(Sort,TermServices)}.
     */
    public static final Name CAST_NAME = new Name("cast");

    /**
     * Name of {@link #getInstanceofSymbol(Sort,TermServices)}.
     */
    public static final Name INSTANCE_NAME = new Name("instance");

    /** Name of the JavaDL theory */
    public static final Name NAME = new Name("JavaDLTheory");
    /**
     * Formulas are represented as "terms" of this sort.
     */
    public static final Sort FORMULA = new SortImpl(new Name("Formula"));
    /**
     * Updates are represented as "terms" of this sort.
     */
    public static final Sort UPDATE = new SortImpl(new Name("Update"));
    /**
     * Term labels are represented as "terms" of this sort.
     */
    public static final Sort TERMLABEL = new SortImpl(new Name("TermLabel"));
    /**
     * Any is a supersort of all sorts.
     */
    public static final Sort ANY = new SortImpl(new Name("any"));

    // TODO fix wrong tests (which do not use proper services)
    // private final TermServices services;

    protected JavaDLTheory(TermServices services) {
        super(NAME, FORMULA, services);
        // this.services = services;
    }

    /*
     * aus NullSort
     *
     * @Override
     * public SortDependingFunction getCastSymbol(TermServices services, Sort sort) {
     * SortDependingFunction result = SortDependingFunction.getFirstInstance(JavaDLTheory.CAST_NAME,
     * services)
     * .getInstanceFor(this, services);
     * assert result.getSortDependingOn() == sort && result.sort() == sort;
     * return result;
     * }
     *
     *
     * @Override
     * public SortDependingFunction getInstanceofSymbol(TermServices services, Sort sort) {
     * SortDependingFunction result = SortDependingFunction
     * .getFirstInstance(JavaDLTheory.INSTANCE_NAME, services).getInstanceFor(this, services);
     * assert result.getSortDependingOn() == sort;
     * return result;
     * }
     *
     *
     * @Override
     * public SortDependingFunction getExactInstanceofSymbol(TermServices services, Sort sort) {
     * SortDependingFunction result = SortDependingFunction
     * .getFirstInstance(JavaDLTheory.EXACT_INSTANCE_NAME, services).getInstanceFor(this, services);
     * assert result.getSortDependingOn() == sort;
     * return result;
     * }
     */

    /**
     * retrieves the cast function for the given sort
     *
     * @param sort the Sort for which to retrieve the cast function
     * @param services the TermServices for lookup
     * @return the found cast function
     */
    public final SortDependingFunction getCastSymbol(Sort sort, TermServices services) {
        SortDependingFunction castFunction =
            SortDependingFunction.getFirstInstance(CAST_NAME, services);
        if (castFunction == null) {
            throw new IllegalStateException("No 'cast' function found for any type.");
        }
        SortDependingFunction result = castFunction.getInstanceFor(sort, services);
        assert result.getSortDependingOn() == sort && result.sort() == sort;
        return result;
    }

    /**
     * retrieves the instanceof function for the given sort
     *
     * @param sort the Sort for which to retrieve the instanceof function
     * @param services the TermServices for lookup
     * @return the found instanceof function
     */
    public final SortDependingFunction getInstanceofSymbol(Sort sort, TermServices services) {
        SortDependingFunction result = SortDependingFunction
                .getFirstInstance(INSTANCE_NAME, services)
                .getInstanceFor(sort, services);
        assert result.getSortDependingOn() == sort;
        return result;
    }


    /**
     * retrieves the exactInstance function for the given sort
     *
     * @param sort the Sort for which to retrieve the exactInstance function
     * @param services the TermServices for lookup
     * @return the found exactInstance function
     */
    public final SortDependingFunction getExactInstanceofSymbol(Sort sort, TermServices services) {
        SortDependingFunction result = SortDependingFunction
                .getFirstInstance(EXACT_INSTANCE_NAME, services)
                .getInstanceFor(sort, services);
        assert result.getSortDependingOn() == sort;
        return result;
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
    public JFunction getFunctionFor(Operator op, Services services, ExecutionContext ec) {
        assert false;
        return null;
    }

    @Override
    public boolean hasLiteralFunction(JFunction f) {
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
