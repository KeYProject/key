/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.ldt;

import java.util.Map;
import java.util.TreeMap;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.sort.ParametricSortDecl;

import org.key_project.logic.Name;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/// An "LDT" or "language data type" class corresponds to a standard rule file shipped with KeY.
/// Usually, this rule file declares a sort (such as "int") and a number of operators. The LDT class
/// provides a programming interface to access these entities, and it assists the type converter in
/// handling them.
///
/// This class is for parametric types, e.g., `Set`.
@NullMarked
public abstract class ParametricLDT extends AbstractLDT {
    /// the main parametric sort associated with the LDT
    private final @Nullable ParametricSortDecl sort;


    protected ParametricLDT(Name name, TermServices services) {
        super(name);
        sort = services.getNamespaces().parametricSorts().lookup(name);
        if (sort == null) {
            throw new RuntimeException("LDT " + name + " not found.\n"
                + "It seems that there are definitions missing from the .key files.");
        }
    }

    /*
     * Use this method to instantiate all LDTs. It returns a map that takes as input the name of an
     * LDT and returns an instance of the corresponding LDT.
     *
     * Is it possible to implement LDTs as singletons? (Kai Wallisch 04/2014)
     */
    public static Map<Name, ParametricLDT> getNewLDTInstances(Services s) {
        // TreeMap ensures the map is sorted according to the natural order of its keys.
        Map<Name, ParametricLDT> ret = new TreeMap<>();

        ret.put(SetLDT.NAME, new SetLDT(s));

        return ret;
    }

    @Override
    public final String toString() {
        return "Parametric LDT " + name() + " (" + targetSort() + ")";
    }

    /**
     * Returns the sort associated with the LDT.
     */
    public final ParametricSortDecl targetSort() {
        return sort;
    }
}
