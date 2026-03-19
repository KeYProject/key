/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang.jml.translation;

import java.util.Map;

import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.op.LocationVariable;

import org.key_project.util.collection.ImmutableList;

/**
 * A collection of all program variables needed to translate a textual JML specification case.
 *
 * Used in {@link JMLSpecFactory}.
 */
public class ProgramVariableCollection {
    /**
     * {@code self}
     */
    public LocationVariable selfVar;

    /**
     * The list of method parameters if the textual specification case is a method contract.
     */
    public ImmutableList<LocationVariable> paramVars;

    /**
     * {@code result}
     */
    public LocationVariable resultVar;

    /**
     * {@code exception}
     */
    public LocationVariable excVar;

    /**
     * A map from every variable {@code var} to {@code \old(var)}.
     */
    public Map<LocationVariable, LocationVariable> atPreVars;

    /**
     * A map from every variable {@code var} to {@code \old(var)}.
     */
    public Map<LocationVariable, JTerm> atPres;

    /**
     * A map from every variable {@code var} to {@code \before(var)} (if applicable).
     */
    public Map<LocationVariable, LocationVariable> atBeforeVars;

    /**
     * A map from every variable {@code var} to {@code \before(var)} (if applicable).
     */
    public Map<LocationVariable, JTerm> atBefores;

    /**
     * Create a collection containing the specified variables.
     *
     * @param selfVar {@code self}
     * @param paramVars the list of method parameters if the textual specification case is a method
     *        contract.
     * @param resultVar {@code result}
     * @param excVar {@code exception}
     * @param atPreVars a map from every variable {@code var} to {@code \old(var)}.
     * @param atPres a map from every variable {@code var} to {@code \old(var)}.
     */
    public ProgramVariableCollection(LocationVariable selfVar,
            ImmutableList<LocationVariable> paramVars, LocationVariable resultVar,
            LocationVariable excVar, Map<LocationVariable, LocationVariable> atPreVars,
            Map<LocationVariable, JTerm> atPres) {
        this(selfVar, paramVars, resultVar, excVar, atPreVars, atPres, null, null);
    }

    /**
     * Create a collection containing the specified variables.
     *
     * @param selfVar {@code self}
     * @param paramVars the list of method parameters if the textual specification case is a method
     *        contract.
     * @param resultVar {@code result}
     * @param excVar {@code exception}
     * @param atPreVars a map from every variable {@code var} to {@code \old(var)}.
     * @param atPres a map from every variable {@code var} to {@code \old(var)}.
     * @param atBeforeVars a map from every variable {@code var} to {@code \before(var)} (if
     *        applicable).
     * @param atBefores a map from every variable {@code var} to {@code \before(var)} (if
     *        applicable).
     */
    public ProgramVariableCollection(LocationVariable selfVar,
            ImmutableList<LocationVariable> paramVars, LocationVariable resultVar,
            LocationVariable excVar, Map<LocationVariable, LocationVariable> atPreVars,
            Map<LocationVariable, JTerm> atPres,
            Map<LocationVariable, LocationVariable> atBeforeVars,
            Map<LocationVariable, JTerm> atBefores) {
        super();
        this.selfVar = selfVar;
        this.paramVars = paramVars;
        this.resultVar = resultVar;
        this.excVar = excVar;
        this.atPreVars = atPreVars;
        this.atPres = atPres;
        this.atBeforeVars = atBeforeVars;
        this.atBefores = atBefores;
    }

    /**
     * Create an empty collection.
     */
    public ProgramVariableCollection() {
    }
}
