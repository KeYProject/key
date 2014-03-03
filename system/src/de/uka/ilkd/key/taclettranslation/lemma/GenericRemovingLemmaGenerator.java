package de.uka.ilkd.key.taclettranslation.lemma;

import java.util.HashMap;
import java.util.Map;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.SortDependingFunction;
import de.uka.ilkd.key.logic.sort.GenericSort;
import de.uka.ilkd.key.logic.sort.ProxySort;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * Generic removing lemma generator adds the default implementation only that all
 * {@link GenericSort}s are replaced to equally named {@link ProxySort}s.
 *
 * <p>This is done since the resulting term is to be used as a proof obligation
 * in which generic sorts must not appear; proxy sorts, however, may.
 *
 * For every generic sort, precisely one proxy sort is introduced.
 */
public class GenericRemovingLemmaGenerator extends DefaultLemmaGenerator {

    /**
     * The map from generic sorts to proxy sorts.
     */
    private final Map<Sort, Sort> sortMap = new HashMap<Sort, Sort>();


    /** {@inheritDoc}
     * <p>
     * The generic removing implementation replaces sort depending functions
     * if their sort argument is a generic sort.
     */
    @Override
    protected Operator replaceOp(Operator op, TermServices services) {

        if (op instanceof SortDependingFunction) {
            SortDependingFunction sdf = (SortDependingFunction) op;
            Sort sort = sdf.getSortDependingOn();
            Sort repSort = replaceSort(sort, services);
            if(sort != repSort) {
                op = sdf.getInstanceFor(repSort, services);
            }
        }

        return op;
    }

    /**
     * {@inheritDoc}
     *
     * <p>
     * The generic removing implementation replaces generic sorts by equally
     * named proxy sorts.
     */
    @Override
    protected Sort replaceSort(Sort sort, TermServices services) {
        if(sort instanceof GenericSort) {

            Sort cached = sortMap.get(sort);
            if(cached != null) {
                return cached;
            }

            ImmutableSet<Sort> extSorts = replaceSorts(sort.extendsSorts(), services);
            ProxySort result = new ProxySort(sort.name(), extSorts);
            sortMap.put(sort, result);
            return result;

        } else {
            return sort;
        }
    }

    /**
     * Replace sorts.
     *
     * @param extendsSorts
     *            the extends sorts
     * @param services
     *            the services
     * @return the immutable set
     */
    private ImmutableSet<Sort> replaceSorts(ImmutableSet<Sort> extendsSorts, TermServices services) {
        ImmutableSet<Sort> result = DefaultImmutableSet.nil();
        for (Sort sort : extendsSorts) {
            result = result.add(replaceSort(sort, services));
        }
        return result;
    }
}