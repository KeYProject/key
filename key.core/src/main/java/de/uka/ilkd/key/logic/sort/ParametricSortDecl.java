/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.sort;

import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.logic.GenericParameter;

import org.key_project.logic.Name;
import org.key_project.logic.Named;
import org.key_project.logic.sort.Sort;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;
import org.key_project.util.collection.Immutables;

import org.jspecify.annotations.NonNull;

public class ParametricSortDecl implements Named {
    private final Name name;
    private final boolean isAbstract;
    private final String documentation;

    private final ImmutableList<GenericParameter> parameters;
    private final ImmutableSet<Sort> extendedSorts;
    private final String origin;

    public ParametricSortDecl(Name name, boolean isAbstract, ImmutableSet<Sort> ext,
            ImmutableList<GenericParameter> sortParams, String documentation, String origin) {
        this.name = name;
        this.isAbstract = isAbstract;
        this.extendedSorts = ext.isEmpty() ? ImmutableSet.singleton(JavaDLTheory.ANY) : ext;
        this.documentation = documentation;
        this.parameters = sortParams;
        this.origin = origin;
        assert Immutables.isDuplicateFree(parameters)
                : "The caller should have made sure that generic sorts are not duplicated";
    }

    public ImmutableList<GenericParameter> getParameters() {
        return parameters;
    }

    @Override
    public @NonNull Name name() {
        return name;
    }

    public boolean isAbstract() {
        return isAbstract;
    }

    public ImmutableSet<Sort> getExtendedSorts() {
        return extendedSorts;
    }

    public String getDocumentation() {
        return documentation;
    }

    public String getOrigin() {
        return origin;
    }
}
