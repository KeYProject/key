/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.sort;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.SortDependingFunction;
import de.uka.ilkd.key.rule.HasOrigin;

import org.key_project.util.collection.ImmutableSet;

import org.jspecify.annotations.Nullable;


public interface Sort extends Named, HasOrigin {

    /**
     * Formulas are represented as "terms" of this sort.
     */
    Sort FORMULA = new SortImpl(new Name("Formula"), null, "", "");

    /**
     * Updates are represented as "terms" of this sort.
     */
    Sort UPDATE = new SortImpl(new Name("Update"), null, "", "");

    /**
     * Term labels are represented as "terms" of this sort.
     */
    Sort TERMLABEL = new SortImpl(new Name("TermLabel"), null, "", "");

    /**
     * Any is a supersort of all sorts.
     */
    Sort ANY = new SortImpl(new Name("any"), null, "", "");

    /**
     * The base name for the cast function family.
     * Individual functions are called e.g. "C::cast" for sort C.
     */
    Name CAST_NAME = new Name("cast");

    /**
     * The base name for the instance (type membership) function family.
     * Individual functions are called e.g. "C::instance" for sort C.
     */
    Name INSTANCE_NAME = new Name("instance");

    /**
     * The base name for the exact type membership function family.
     * Individual functions are called e.g. "C::exactInstace" for sort C.
     */
    Name EXACT_INSTANCE_NAME = new Name("exactInstance");

    /**
     * @return the direct supersorts of this sort. Not supported by {@code NullSort}.
     */
    ImmutableSet<Sort> extendsSorts();

    /**
     * @param services services.
     * @return the direct supersorts of this sort.
     */
    ImmutableSet<Sort> extendsSorts(Services services);

    /**
     * @param s some sort.
     * @return whether the given sort is a reflexive, transitive subsort of this sort.
     */
    boolean extendsTrans(Sort s);

    /**
     * @return whether this sort has no exact elements.
     */
    boolean isAbstract();

    /**
     * @param services services.
     * @return the cast symbol of this sort.
     */
    default SortDependingFunction getCastSymbol(TermServices services) {
        SortDependingFunction result
                = SortDependingFunction.getFirstInstance(CAST_NAME, services)
                .getInstanceFor(this, services);
        assert result.getSortDependingOn() == this && result.sort() == this;
        return result;
    }

    /**
     * @param services services.
     * @return the {@code instanceof} symbol of this sort.
     */
    default SortDependingFunction getInstanceofSymbol(TermServices services) {
        SortDependingFunction result
                = SortDependingFunction.getFirstInstance(INSTANCE_NAME, services)
                .getInstanceFor(this, services);
        assert result.getSortDependingOn() == this;
        return result;
    }

    /**
     * @param services services.
     * @return the {@code exactinstanceof} symbol of this sort.
     */
    default SortDependingFunction getExactInstanceofSymbol(TermServices services)     {
        SortDependingFunction result
                = SortDependingFunction.getFirstInstance(EXACT_INSTANCE_NAME, services)
                .getInstanceFor(this, services);
        assert result.getSortDependingOn() == this;
        return result;
    }

    /**
     * returns the string to be used for declarations.
     *
     * As of Dec 2018, all implementations use {@link #name()} for this value.
     */
    default String declarationString() {
        return name().toString();
    }

    /**
     * Returns an human explainable text describing this sort. This field is typical set by the
     * parser, who captures the documentation comments.
     */
    @Nullable
    default String getDocumentation() { return null; }
}
