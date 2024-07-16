/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.parser.builder;

import org.key_project.logic.Name;
import org.key_project.logic.Named;
import org.key_project.logic.Namespace;
import org.key_project.logic.op.Function;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.logic.sort.Sort;
import org.key_project.rusty.Services;
import org.key_project.rusty.logic.NamespaceSet;
import org.key_project.rusty.logic.op.ProgramVariable;

import org.jspecify.annotations.NonNull;

public class DefaultBuilder extends AbstractBuilder<Object> {
    protected final Services services;
    protected final NamespaceSet nss;


    public DefaultBuilder(Services services, NamespaceSet nss) {
        this.services = services;
        this.nss = nss;
    }

    protected Named lookup(Name n) {
        final Namespace<?>[] lookups =
            { programVariables(), variables(), functions() };
        return doLookup(n, lookups);
    }

    protected <T> T doLookup(Name n, Namespace<?>... lookups) {
        for (Namespace<?> lookup : lookups) {
            Object l;
            if (lookup != null && (l = lookup.lookup(n)) != null) {
                try {
                    return (T) l;
                } catch (ClassCastException e) {
                }
            }
        }
        return null;
    }

    public NamespaceSet namespaces() {
        return nss;
    }

    protected Namespace<@NonNull QuantifiableVariable> variables() {
        return namespaces().variables();
    }

    protected Namespace<Sort> sorts() {
        return namespaces().sorts();
    }

    protected Namespace<Function> functions() {
        return namespaces().functions();
    }

    protected Namespace<ProgramVariable> programVariables() {
        return namespaces().programVariables();
    }
}
