/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.ldt;

import java.util.Map;
import java.util.TreeMap;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.abstraction.Type;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.sort.SortAlias;

import org.key_project.logic.Name;
import org.key_project.logic.sort.Sort;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * An "LDT" or "language data type" class corresponds to a standard rule file shipped with KeY.
 * Usually, this rule file declares a sort (such as "int") and a number of operators. The LDT class
 * provides a programming interface to access these entities, and it assists the type converter in
 * handling them.
 */
@NullMarked
public abstract class LDT extends AbstractLDT {
    /**
     * the main sort associated with the LDT
     */
    protected final @Nullable Sort sort;

    // -------------------------------------------------------------------------
    // constructors
    // -------------------------------------------------------------------------

    protected LDT(Name name, TermServices services) {
        super(name);
        var sort = services.getNamespaces().sorts().lookup(name);
        if (sort == null) {
            SortAlias alias = services.getNamespaces().sortAliases().lookup(name);
            sort = alias == null ? null : alias.aliasedSort();
            if (sort == null) {
                throw new RuntimeException("LDT " + name + " not found.\n"
                    + "It seems that there are definitions missing from the .key files.");
            }
        }
        this.sort = sort;
    }


    protected LDT(Name name, @Nullable Sort targetSort) {
        super(name);
        sort = targetSort;
        if (sort == null) {
            throw new RuntimeException("LDT " + name + " not found.\n"
                + "It seems that there are definitions missing from the .key files.");
        }
    }

    // -------------------------------------------------------------------------
    // protected methods
    // -------------------------------------------------------------------------

    // -------------------------------------------------------------------------
    // public methods
    // -------------------------------------------------------------------------

    /*
     * Use this method to instantiate all LDTs. It returns a map that takes as input the name of an
     * LDT and returns an instance of the corresponding LDT.
     *
     * Is it possible to implement LDTs as singletons? (Kai Wallisch 04/2014)
     */
    public static Map<Name, LDT> getNewLDTInstances(Services s) {
        // TreeMap ensures the map is sorted according to the natural order of its keys.
        Map<Name, LDT> ret = new TreeMap<>();

        ret.put(JavaDLTheory.NAME, new JavaDLTheory(s));
        ret.put(IntegerLDT.NAME, new IntegerLDT(s));
        ret.put(BooleanLDT.NAME, new BooleanLDT(s));
        ret.put(LocSetLDT.NAME, new LocSetLDT(s));
        ret.put(HeapLDT.NAME, new HeapLDT(s));
        ret.put(PermissionLDT.NAME, new PermissionLDT(s));
        ret.put(SeqLDT.NAME, new SeqLDT(s));
        ret.put(SortLDT.NAME, new SortLDT(s));
        ret.put(FreeLDT.NAME, new FreeLDT(s));
        ret.put(MapLDT.NAME, new MapLDT(s));
        ret.put(FloatLDT.NAME, new FloatLDT(s));
        ret.put(DoubleLDT.NAME, new DoubleLDT(s));
        ret.put(RealLDT.NAME, new RealLDT(s));
        ret.put(CharListLDT.NAME, new CharListLDT(s));

        return ret;
    }

    @Override
    public final String toString() {
        return "LDT " + name() + " (" + targetSort() + ")";
    }

    /**
     * Returns the sort associated with the LDT.
     */
    public final Sort targetSort() {
        return sort;
    }

    // -------------------------------------------------------------------------
    // abstract methods
    // -------------------------------------------------------------------------


    public abstract Type getType(JTerm t);
}
