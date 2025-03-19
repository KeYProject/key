/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.sort;

import java.lang.ref.WeakReference;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.JavaDLTheory;

import org.key_project.logic.LogicServices;
import org.key_project.logic.Name;
import org.key_project.logic.sort.Sort;
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
public final class NullSort extends SortImpl {

    public static final Name NAME = new Name("Null");

    private final Sort objectSort;

    private WeakReference<Services> lastServices = new WeakReference<>(null);
    private WeakReference<ImmutableSet<Sort>> extCache =
        new WeakReference<>(null);


    public NullSort(Sort objectSort) {
        super(NAME, null, false, "", "");
        assert objectSort != null;
        this.objectSort = objectSort;
    }


    @Override
    public ImmutableSet<Sort> extendsSorts() {
        throw new UnsupportedOperationException("NullSort.extendsSorts() cannot be supported");
    }


    @Override
    public <S extends LogicServices> ImmutableSet<Sort> extendsSorts(S p_services) {
        final Services services = (Services) p_services;
        assert services != null;
        assert objectSort == services.getJavaInfo().objectSort();

        ImmutableSet<Sort> result = extCache.get();
        if (result == null || lastServices.get() != services) {
            result = DefaultImmutableSet.nil();

            for (Sort n : services.getNamespaces().sorts().allElements()) {
                if (n != this && n.extendsTrans(objectSort)) {
                    result = result.add(n);
                }
            }

            lastServices = new WeakReference<>(services);
            extCache = new WeakReference<>(result);
        }

        return result;
    }

    @Override
    public boolean extendsTrans(Sort sort) {
        return sort == this || sort == JavaDLTheory.ANY || sort.extendsTrans(objectSort);
    }

    @Override
    public String declarationString() {
        return NAME.toString();
    }
}
