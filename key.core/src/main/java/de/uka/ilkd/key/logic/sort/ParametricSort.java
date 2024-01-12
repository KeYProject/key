package de.uka.ilkd.key.logic.sort;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.util.Pair;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;

import java.util.IdentityHashMap;
import java.util.Map;
import java.util.function.Function;
import java.util.stream.Collectors;

/**
 *
 * Here is a short class diagram, written for PlantUML.
 * You can create the PNG file by feeding this SourceFile into PlantUML or
 * by entering the text into https://www.planttext.com/, e.g.
 *
 * @startuml
 *
 * interface Sort
 * abstract class AbstractSort
 * class SortImpl
 *
 * class PolymorphicSort
 * class PolymorphicSortInstance
 * class NullSort
 * class GenericSort
 *
 * Sort <|-- AbstractSort
 * AbstractSort <|-- SortImpl
 * AbstractSort <|-- PolymorphicSort
 * AbstractSort <|-- GenericSort
 * Sort <|-- PolymorphicSortInstance
 * Sort <|-- NullSort
 *
 * PolymorphicSortInstance --> "1" PolymorphicSort : base
 * PolymorphicSortInstance --> "*" Sort :args
 * PolymorphicSort --> "*" GenericSort : typeParameters
 *
 *
 * PolymorphicSort : bounds : List[Variance]
 *
 * enum Variance {
 *   COVARIANT
 *   CONTRAVARIANT
 *   INVARIANT
 * }
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

    public ParametricSort(Name name, ImmutableSet<Sort> ext, boolean isAbstract,
                          ImmutableList<GenericSort> parameters, ImmutableList<Variance> covariances,
                          String documentation, String origin) {
        super(name, ext, isAbstract, documentation, origin);
        this.parameters = parameters;
        this.covariances = covariances;
    }

    public ParametricSort(Name name, ImmutableSet<Sort> ext, boolean isAbstract,
                          ImmutableList<Pair<GenericSort, Variance>> sortParams) {
        this(name, ext, isAbstract, sortParams.map(x -> x.first), sortParams.map(x -> x.second), null, null);
    }

    public Function<Sort, Sort> getInstantiation(ImmutableList<Sort> args) {
        IdentityHashMap<GenericSort, Sort> map = new IdentityHashMap<>();

        if(args.size() != parameters.size()) {
            throw new IllegalArgumentException("Parametric type " + name() +
                    " expected " + parameters.size() + " arguments, but received " +
                    args);
        }

        ImmutableList<GenericSort> p = parameters;
        while(!args.isEmpty()) {
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
            if(mapped != null) {
                return mapped;
            }
            if (sort instanceof ParametricSortInstance) {
                ParametricSortInstance psort = (ParametricSortInstance) sort;
                return psort.map(this::apply);
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
}
