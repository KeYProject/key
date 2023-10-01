/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.sort;

import java.lang.ref.WeakReference;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.SortDependingFunction;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableSet;


/**
 * There is one instance of this class per proof, representing the sort "Null". This sort is a
 * subsort of all object sorts. Unfortunately, NullSort sometimes has to be treated as a special
 * case, because it cannot support the method extendsSorts() (without a Services parameter) -- for
 * this, the object would have to "know" all the object sorts, but these sorts are created only
 * after the NullSort object itself has to be created; and immutability prevents us from filling in
 * this information later.
 */
public final class NullSort implements Sort {

    public static final Name NAME = new Name("Null");

    private final Sort objectSort;

    private WeakReference<Services> lastServices = new WeakReference<>(null);
    private WeakReference<ImmutableSet<Sort>> extCache =
        new WeakReference<>(null);


    public NullSort(Sort objectSort) {
        assert objectSort != null;
        this.objectSort = objectSort;
    }


    @Override
    public Name name() {
        return NAME;
    }


    @Override
    public ImmutableSet<Sort> extendsSorts() {
        throw new UnsupportedOperationException("NullSort.extendsSorts() cannot be supported");
    }


    @Override
    public ImmutableSet<Sort> extendsSorts(Services services) {
        assert services != null;
        assert objectSort == services.getJavaInfo().objectSort();

        ImmutableSet<Sort> result = extCache.get();
        if (result == null || lastServices.get() != services) {
            result = DefaultImmutableSet.nil();

            for (Sort n : services.getNamespaces().sorts().allElements()) {
                Sort s = n;
                if (s != this && s.extendsTrans(objectSort)) {
                    result = result.add(s);
                }
            }

            lastServices = new WeakReference<>(services);
            extCache = new WeakReference<>(result);
        }

        return result;
    }


    @Override
    public boolean extendsTrans(Sort sort) {
        return sort == this || sort == Sort.ANY || sort.extendsTrans(objectSort);
    }


    @Override
    public boolean isAbstract() {
        return false;
    }


    @Override
    public SortDependingFunction getCastSymbol(TermServices services) {
        SortDependingFunction result = SortDependingFunction.getFirstInstance(CAST_NAME, services)
                .getInstanceFor(this, services);
        assert result.getSortDependingOn() == this && result.sort() == this;
        return result;
    }


    @Override
    public SortDependingFunction getInstanceofSymbol(TermServices services) {
        SortDependingFunction result = SortDependingFunction
                .getFirstInstance(INSTANCE_NAME, services).getInstanceFor(this, services);
        assert result.getSortDependingOn() == this;
        return result;
    }


    @Override
    public SortDependingFunction getExactInstanceofSymbol(TermServices services) {
        SortDependingFunction result = SortDependingFunction
                .getFirstInstance(EXACT_INSTANCE_NAME, services).getInstanceFor(this, services);
        assert result.getSortDependingOn() == this;
        return result;
    }


    @Override
    public String toString() {
        return NAME.toString();
    }

    @Override
    public String declarationString() {
        return NAME.toString();
    }
}
