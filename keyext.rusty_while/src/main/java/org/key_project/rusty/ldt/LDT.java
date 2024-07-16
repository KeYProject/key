/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ldt;

import org.key_project.logic.Name;
import org.key_project.logic.Named;
import org.key_project.logic.Namespace;
import org.key_project.logic.op.Function;
import org.key_project.logic.op.Operator;
import org.key_project.logic.sort.Sort;
import org.key_project.rusty.Services;

import org.jspecify.annotations.NonNull;

public abstract class LDT implements Named {
    private final Name name;

    /** the main sort associated with the LDT */
    private final Sort sort;

    /** the namespace of functions this LDT feels responsible for */
    private final Namespace<@NonNull Operator> functions = new Namespace<>();

    // -------------------------------------------------------------------------
    // constructors
    // -------------------------------------------------------------------------

    protected LDT(Name name, Services services) {
        sort = services.getNamespaces().sorts().lookup(name);
        if (sort == null) {
            throw new RuntimeException("LDT " + name + " not found.\n"
                + "It seems that there are definitions missing from the .key files.");
        }
        this.name = name;
    }


    protected LDT(Name name, Sort targetSort, Services services) {
        sort = targetSort;
        if (sort == null) {
            throw new RuntimeException("LDT " + name + " not found.\n"
                + "It seems that there are definitions missing from the .key files.");
        }
        this.name = name;
    }

    // -------------------------------------------------------------------------
    // protected methods
    // -------------------------------------------------------------------------

    /**
     * adds a function to the LDT
     *
     * @return the added function (for convenience reasons)
     */
    protected final Function addFunction(Function f) {
        functions.addSafely(f);
        return f;
    }

    /**
     * looks up a function in the namespace and adds it to the LDT
     *
     * @param funcName the String with the name of the function to look up
     * @return the added function (for convenience reasons)
     */
    protected final Function addFunction(Services services, String funcName) {
        final Namespace<@NonNull Function> funcNS = services.getNamespaces().functions();
        final Function f = funcNS.lookup(new Name(funcName));
        if (f == null) {
            throw new RuntimeException("LDT: Function " + funcName + " not found.\n"
                + "It seems that there are definitions missing from the .key files.");
        }
        return addFunction(f);
    }
}
