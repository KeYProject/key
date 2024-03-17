/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.sort;

import java.util.IdentityHashMap;
import java.util.Map;
import java.util.function.Function;

import de.uka.ilkd.key.ldt.JavaDLTheory;

import org.key_project.logic.Name;
import org.key_project.logic.sort.AbstractSort;
import org.key_project.logic.sort.Sort;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;

/**
 * Here is a short class diagram, written for PlantUML.
 * You can create the PNG file by feeding this SourceFile into PlantUML or
 * by entering the text into https://www.planttext.com/, e.g.
 *
 * @startuml interface Sort
 *           abstract class AbstractSort
 *           class SortImpl
 *           <p>
 *           class PolymorphicSort
 *           class PolymorphicSortInstance
 *           class NullSort
 *           class GenericSort
 *           <p>
 *           Sort <|-- AbstractSort
 *           AbstractSort <|-- SortImpl
 *           AbstractSort <|-- PolymorphicSort
 *           AbstractSort <|-- GenericSort
 *           Sort <|-- PolymorphicSortInstance
 *           Sort <|-- NullSort
 *           <p>
 *           PolymorphicSortInstance --> "1" PolymorphicSort : base
 *           PolymorphicSortInstance --> "*" Sort :args
 *           PolymorphicSort --> "*" GenericSort : typeParameters
 *           <p>
 *           <p>
 *           PolymorphicSort : bounds : List[Variance]
 *           <p>
 *           enum Variance {
 *           COVARIANT
 *           CONTRAVARIANT
 *           INVARIANT
 *           }
 * @enduml
 */

public class ParametricSort extends AbstractSort {
    public enum Variance {
        COVARIANT,
        CONTRAVARIANT,
        INVARIANT;
    }

    private final ImmutableList<GenericSort> parameters;

    private final ImmutableList<Variance> covariances;

    private final ImmutableSet<Sort> extendsSorts;

    public ParametricSort(Name name, ImmutableSet<Sort> ext, boolean isAbstract,
            ImmutableList<GenericSort> parameters, ImmutableList<Variance> covariances,
            String documentation, String origin) {
        super(name, isAbstract, origin, documentation);
        this.extendsSorts = ext;
        this.parameters = parameters;
        this.covariances = covariances;
    }

    public record SortParameter(GenericSort first, Variance second) {
    }

    public ParametricSort(Name name, ImmutableSet<Sort> ext, boolean isAbstract,
            ImmutableList<SortParameter> sortParams) {
        this(name, ext, isAbstract, sortParams.map(x -> x.first), sortParams.map(x -> x.second),
            null, null);
    }

    public Function<Sort, Sort> getInstantiation(ImmutableList<Sort> args) {
        IdentityHashMap<GenericSort, Sort> map = new IdentityHashMap<>();

        if (args.size() != parameters.size()) {
            throw new IllegalArgumentException("Parametric type " + name() +
                " expected " + parameters.size() + " arguments, but received " +
                args);
        }

        ImmutableList<GenericSort> p = parameters;
        while (!args.isEmpty()) {
            map.put(p.head(), args.head());
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

    public ImmutableList<GenericSort> getParameters() {
        return parameters;
    }

    public ImmutableList<Variance> getCovariances() {
        return covariances;
    }

    @Override
    public ImmutableSet<Sort> extendsSorts() {
        return extendsSorts;
    }

    @Override
    public boolean extendsTrans(Sort sort) {
        if (sort == this) {
            return true;
        } else if (this == JavaDLTheory.FORMULA || this == JavaDLTheory.UPDATE) {
            return false;
        } else if (sort == JavaDLTheory.ANY) {
            return true;
        }

        return extendsSorts()
                .exists((Sort superSort) -> superSort == sort || superSort.extendsTrans(sort));
    }
}
