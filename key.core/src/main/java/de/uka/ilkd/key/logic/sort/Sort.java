/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.sort;

import javax.annotation.Nullable;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.SortDependingFunction;
import de.uka.ilkd.key.rule.HasOrigin;

import org.key_project.util.collection.ImmutableSet;


public interface Sort extends Named, HasOrigin {

    /**
     * Formulas are represented as "terms" of this sort.
     */
    Sort FORMULA = new SortImpl(new Name("Formula"));

    /**
     * Updates are represented as "terms" of this sort.
     */
    Sort UPDATE = new SortImpl(new Name("Update"));

    /**
     * Term labels are represented as "terms" of this sort.
     */
    Sort TERMLABEL = new SortImpl(new Name("TermLabel"));

    /**
     * Any is a supersort of all sorts.
     */
    Sort ANY = new SortImpl(new Name("any"));

    /**
     * Name of {@link #getCastSymbol(TermServices)}.
     */
    Name CAST_NAME = new Name("cast");

    /**
     * Name of {@link #getInstanceofSymbol(TermServices)}.
     */
    Name INSTANCE_NAME = new Name("instance");

    /**
     * Name of {@link #getExactInstanceofSymbol(TermServices)}.
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
    SortDependingFunction getCastSymbol(TermServices services);

    /**
     * @param services services.
     * @return the {@code instanceof} symbol of this sort.
     */
    SortDependingFunction getInstanceofSymbol(TermServices services);

    /**
     * @param services services.
     * @return the {@code exactinstanceof} symbol of this sort.
     */
    SortDependingFunction getExactInstanceofSymbol(TermServices services);

    String declarationString();

    /**
     * Returns an human explainable text describing this sort. This field is typical set by the
     * parser, who captures the documentation comments.
     */
    @Nullable
    default String getDocumentation() { return null; }
}
