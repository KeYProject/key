/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.nparser;


import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.logic.sort.SortImpl;

/**
 * @author Alexander Weigl
 * @version 1 (17.10.19)
 */
public class NamespaceBuilder {
    private final NamespaceSet nss;

    public NamespaceBuilder(NamespaceSet nss) {
        this.nss = nss;
    }

    public NamespaceBuilder addSort(String name) {
        nss.sorts().add(new SortImpl(new Name(name)));
        return this;
    }

    private Sort getOrCreateSort(String group) {
        if (nss.sorts().lookup(group) == null) {
            addSort(group);
        }
        return nss.sorts().lookup(group);
    }

    public NamespaceBuilder addVariable(String name, String sort) {
        nss.variables().add(new LogicVariable(new Name(name), getOrCreateSort(sort)));
        return this;
    }

    public NamespaceBuilder addProgramVariable(String sort, String varName) {
        Sort s = getOrCreateSort(sort);
        ProgramVariable pv = new LocationVariable(new ProgramElementName(varName), s);
        nss.programVariables().add(pv);
        return this;
    }
}
