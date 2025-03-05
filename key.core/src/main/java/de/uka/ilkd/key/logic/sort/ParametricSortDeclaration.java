/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.sort;

import java.util.IdentityHashMap;
import java.util.Map;
import java.util.function.Function;

import de.uka.ilkd.key.ldt.JavaDLTheory;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.NullMarked;
import org.key_project.logic.Name;
import org.key_project.logic.Named;
import org.key_project.logic.sort.Sort;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;
import org.key_project.util.collection.Immutables;

/**
 * Here is a short class diagram, written for PlantUML.
 * You can create the PNG file by feeding this SourceFile into PlantUML or
 * by entering the text into https://www.planttext.com/, e.g.
  @formatter:off
  @startuml
  interface Sort
  abstract class AbstractSort
  class SortImpl

  class ParametricSortDeclaration
  class ParametricSortInstance
  class NullSort
  class GenericSort

  Sort <|-- AbstractSort
  AbstractSort <|-- SortImpl
  AbstractSort <|-- ParametricSortInstance
  AbstractSort <|-- GenericSort
  Sort <|-- NullSort

  ParametricSortInstance --> ParametricSortDeclaration : base
  ParametricSortInstance --> "*" Sort :args
  ParametricSortDeclaration --> "n" GenericSort : typeParameters
  ParametricSortDeclaration --> "*" Sort : extendsDecl
  ParametricSortDeclaration --> "n" Variance : variances

  enum Variance {
    COVARIANT
    CONTRAVARIANT
    INVARIANT
  }
  @enduml
  @formatter:on
 */

@NullMarked
public class ParametricSortDeclaration implements Named {

    private final Name name;
    private final boolean isAbstract;
    private final String documentation;
    private final String origin;

    public enum Variance {
        COVARIANT,
        CONTRAVARIANT,
        INVARIANT;
    }

    public record SortParameter(@NonNull GenericSort genericSort, @NonNull Variance variance) {
    }

    private final ImmutableList<SortParameter> parameters;

    private final ImmutableSet<Sort> extendedSorts;

    public ParametricSortDeclaration(Name name, ImmutableSet<Sort> ext, boolean isAbstract,
            ImmutableList<GenericSort> parameters, ImmutableList<Variance> covariances,
            String documentation, String origin) {
        this(name, ext, isAbstract, Immutables.zip(parameters, covariances, SortParameter::new), documentation, origin);
    }

    public ParametricSortDeclaration(Name name, ImmutableSet<Sort> ext, boolean isAbstract,
            ImmutableList<SortParameter> sortParams, String documentation, String origin) {
        this.name = name;
        this.extendedSorts = ext.isEmpty() ? Immutables.setOf(JavaDLTheory.ANY) : ext;
        this.isAbstract = isAbstract;
        this.documentation = documentation;
        this.origin = origin;
        this.parameters = sortParams;
        assert Immutables.isDuplicateFree(parameters.map(SortParameter::genericSort)) :
                "The caller should have made sure that generic sorts are not duplicated";
    }

    public Function<Sort, Sort> getInstantiator(ImmutableList<Sort> args) {
        IdentityHashMap<GenericSort, Sort> map = new IdentityHashMap<>();

        if (args.size() != parameters.size()) {
            throw new IllegalArgumentException("Parametric type " + name +
                " expected " + parameters.size() + " arguments, but received " +
                args);
        }

        ImmutableList<SortParameter> p = parameters;
        while (!args.isEmpty()) {
            map.put(p.head().genericSort(), args.head());
            p = p.tail();
            args = args.tail();
        }

        return new SortInstantiator(map);
    }

    public static class SortInstantiator implements Function<Sort, Sort> {
        private final Map<GenericSort, Sort> map;

        public SortInstantiator(Map<GenericSort, Sort> map) {
            this.map = map;
        }

        @Override
        public Sort apply(Sort sort) {
            Sort mapped = map.get(sort);
            if (mapped != null) {
                return mapped;
            }
            if (sort instanceof ParametricSortInstance psi) {
                return psi.map(this);
            } else {
                return sort;
            }
        }
    }

    public ImmutableList<SortParameter> getParameters() {
        return parameters;
    }

    public ImmutableSet<Sort> getExtendedSorts() {
        return extendedSorts;
    }

    @Override
    public Name name() {
        return name;
    }

    public boolean isAbstract() {
        return isAbstract;
    }

    public String getDocumentation() {
        return documentation;
    }

    public String getOrigin() {
        return origin;
    }
}
