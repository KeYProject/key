// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

/**
 *
 */
package de.uka.ilkd.key.speclang.jml.translation;

import java.util.Map;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;

/**
 * A collection of all program variables needed to translate a textual JML specification case.
 *
 * Used in {@link JMLSpecFactory}.
 */
public class ProgramVariableCollection {
    /**
     * {@code self}
     */
    public ProgramVariable selfVar;

    /**
     * The list of method parameters if the textual specification case is a method contract.
     */
    public ImmutableList<ProgramVariable> paramVars;

    /**
     * {@code result}
     */
    public ProgramVariable resultVar;

    /**
     * {@code exception}
     */
    public ProgramVariable excVar;

    /**
     * A map from every variable {@code var} to {@code \old(var)}.
     */
    public Map<LocationVariable, LocationVariable> atPreVars;

    /**
     * A map from every variable {@code var} to {@code \old(var)}.
     */
    public Map<LocationVariable, Term> atPres;

    /**
     * A map from every variable {@code var} to {@code \before(var)} (if applicable).
     */
    public Map<LocationVariable, LocationVariable> atBeforeVars;

    /**
     * A map from every variable {@code var} to {@code \before(var)} (if applicable).
     */
    public Map<LocationVariable, Term> atBefores;

    /**
     * Create a collection containing the specified variables.
     *
     * @param selfVar
     *            {@code self}
     * @param paramVars
     *            the list of method parameters if the textual specification case is a method
     *            contract.
     * @param resultVar
     *            {@code result}
     * @param excVar
     *            {@code exception}
     * @param atPreVars
     *            a map from every variable {@code var} to {@code \old(var)}.
     * @param atPres
     *            a map from every variable {@code var} to {@code \old(var)}.
     */
    public ProgramVariableCollection(ProgramVariable selfVar,
            ImmutableList<ProgramVariable> paramVars, ProgramVariable resultVar,
            ProgramVariable excVar, Map<LocationVariable, LocationVariable> atPreVars,
            Map<LocationVariable, Term> atPres) {
        this(selfVar, paramVars, resultVar, excVar, atPreVars, atPres, null, null);
    }

    /**
     * Create a collection containing the specified variables.
     *
     * @param selfVar
     *            {@code self}
     * @param paramVars
     *            the list of method parameters if the textual specification case is a method
     *            contract.
     * @param resultVar
     *            {@code result}
     * @param excVar
     *            {@code exception}
     * @param atPreVars
     *            a map from every variable {@code var} to {@code \old(var)}.
     * @param atPres
     *            a map from every variable {@code var} to {@code \old(var)}.
     * @param atBeforeVars
     *            a map from every variable {@code var} to {@code \before(var)} (if applicable).
     * @param atBefores
     *            a map from every variable {@code var} to {@code \before(var)} (if applicable).
     */
    public ProgramVariableCollection(ProgramVariable selfVar,
            ImmutableList<ProgramVariable> paramVars, ProgramVariable resultVar,
            ProgramVariable excVar, Map<LocationVariable, LocationVariable> atPreVars,
            Map<LocationVariable, Term> atPres,
            Map<LocationVariable, LocationVariable> atBeforeVars,
            Map<LocationVariable, Term> atBefores) {
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