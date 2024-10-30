/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.logic.op;

import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.Map;

import org.key_project.logic.Name;
import org.key_project.logic.Term;
import org.key_project.logic.op.AbstractSortedOperator;
import org.key_project.logic.op.Modifier;
import org.key_project.logic.sort.Sort;
import org.key_project.rusty.Services;
import org.key_project.rusty.logic.Place;
import org.key_project.rusty.logic.sort.SortImpl;
import org.key_project.rusty.rule.inst.SVInstantiations;

/**
 * Abstract class factoring out commonalities of typical term transformer implementations. The
 * available singletons of term transformers are kept here.
 */
public abstract class AbstractTermTransformer extends AbstractSortedOperator
        implements TermTransformer {
    // must be first
    /** The metasort sort **/
    public static final Sort METASORT = new SortImpl(new Name("Meta"));

    /** A map from String names to meta operators **/
    public static final Map<String, AbstractTermTransformer> NAME_TO_META_OP =
        new LinkedHashMap<>(5);

    public static final AbstractTermTransformer PV_TO_MUT_REF = new PVToMutRef();

    protected AbstractTermTransformer(Name name, int arity, Sort sort) {
        super(name, createMetaSortArray(arity), sort, Modifier.NONE);
        NAME_TO_META_OP.put(name.toString(), this);
    }

    protected AbstractTermTransformer(Name name, int arity) {
        this(name, arity, METASORT);
    }

    private static Sort[] createMetaSortArray(int arity) {
        Sort[] result = new Sort[arity];
        Arrays.fill(result, METASORT);
        return result;
    }

    public static TermTransformer name2metaop(String s) {
        return NAME_TO_META_OP.get(s);
    }

    private static class PVToMutRef extends AbstractTermTransformer {
        public PVToMutRef() {
            super(new Name("pvToMutRef"), 1);
        }

        @Override
        public Term transform(Term term, SVInstantiations svInst, Services services) {
            var tb = services.getTermBuilder();
            return tb.mutRef(MutRef.getInstance(Place.convertToPlace(term), services));
        }
    }
}
