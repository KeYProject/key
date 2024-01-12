package de.uka.ilkd.key.logic.sort;

import de.uka.ilkd.key.logic.Name;
import org.jspecify.annotations.Nullable;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;

import java.util.Map;
import java.util.Objects;
import java.util.WeakHashMap;
import java.util.function.Function;

public class ParametricSortInstance extends AbstractSort {

    private static Map<ParametricSortInstance, ParametricSortInstance> CACHE = new WeakHashMap<>();

    private final ImmutableList<Sort> parameters;

    private final ParametricSort base;

    public static ParametricSortInstance get(ParametricSort base, ImmutableList<Sort> parameters,
                                             @Nullable String documentation, @Nullable String origin) {
        ParametricSortInstance sort = new ParametricSortInstance(base, parameters, documentation, origin);
        ParametricSortInstance cached = CACHE.get(sort);
        if (cached != null) {
            return cached;
        } else {
            CACHE.put(sort, sort);
            return sort;
        }
    }

    private ParametricSortInstance(ParametricSort base, ImmutableList<Sort> parameters,
                                   String documentation, String origin) {
        super(makeName(base, parameters), computeExt(base, parameters), base.isAbstract(),
                documentation, origin);

        this.base = base;
        this.parameters = parameters;
    }

    private static ImmutableSet<Sort> computeExt(ParametricSort base, ImmutableList<Sort> parameters) {

        ImmutableSet<Sort> result = DefaultImmutableSet.nil();

        // 1. extensions by base sort
        ImmutableSet<Sort> baseExt = base.extendsSorts();
        if(!baseExt.isEmpty()) {
            Function<Sort, Sort> inster = base.getInstantiation(parameters);
            for (Sort s : baseExt) {
                result = result.add(inster.apply(s));
            }
        }

        // 2. extensions by variances
        ImmutableList<ParametricSort.Variance> cov = base.getCovariances();
        for (int i = 0; !cov.isEmpty(); i++, cov = cov.tail()) {
            switch(cov.head()) {
                case COVARIANT:
                    // take all bases of that arg and add the modified sort as ext class
                    for (Sort s : parameters.get(i).extendsSorts()) {
                        ImmutableList<Sort> newArgs = parameters.replace(i, s);
                        result = result.add(ParametricSortInstance.get(base, newArgs, null, null));
                    }
                    break;

                case CONTRAVARIANT:
                    throw new UnsupportedOperationException("Contravariance can currently not be supported");

                case INVARIANT:
                    // Nothing to be done
                    break;
            }
        }

        return result;

    }

    private static Name makeName(Sort base, ImmutableList<Sort> parameters) {
        return new Name(base + "<" + parameters + ">");
    }

    public Sort getBase() {
        return base;
    }

    public ImmutableList<Sort> getParameters() {
        return parameters;
    }

    public ParametricSortInstance map(Function<Sort, Sort> f) {
        ImmutableList<Sort> newParameters = parameters.map(f);
        // The cache ensures that no unnecessary duplicates are kept.
        return get(base, newParameters, null, null);
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        ParametricSortInstance that = (ParametricSortInstance) o;
        return Objects.equals(parameters, that.parameters) &&
                base == that.base;
    }

    @Override
    public int hashCode() {
        return Objects.hash(parameters, base);
    }
}
