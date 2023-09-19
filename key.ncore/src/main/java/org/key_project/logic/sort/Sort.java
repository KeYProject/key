package org.key_project.logic.sort;

import org.key_project.logic.Named;
import org.key_project.logic.Name;
import org.key_project.rule.HasOrigin;
import org.key_project.util.collection.ImmutableSet;

import javax.annotation.Nullable;

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
     * @return the direct supersorts of this sort. Not supported by {@code NullSort}.
     */
    ImmutableSet<Sort> extendsSorts();

    /**
     * @param s some sort.
     * @return whether the given sort is a reflexive, transitive subsort of this sort.
     */
    boolean extendsTrans(Sort s);

    /**
     * @return whether this sort has no exact elements.
     */
    boolean isAbstract();

    String declarationString();

    /**
     * Returns an human explainable text describing this sort. This field is typical set by the
     * parser, who captures the documentation comments.
     */
    @Nullable
    default String getDocumentation() { return null; }
}
