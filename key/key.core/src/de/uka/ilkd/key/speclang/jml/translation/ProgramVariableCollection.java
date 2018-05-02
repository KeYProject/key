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

public class ProgramVariableCollection {
    public ProgramVariable selfVar;
    public ImmutableList<ProgramVariable> paramVars;
    public ProgramVariable resultVar;
    public ProgramVariable excVar;
    public Map<LocationVariable, LocationVariable> atPreVars;
    public Map<LocationVariable, Term> atPres;
    public Map<LocationVariable, LocationVariable> atBeforeVars;
    public Map<LocationVariable, Term> atBefores;

    public ProgramVariableCollection(ProgramVariable selfVar,
                                     ImmutableList<ProgramVariable> paramVars,
                                     ProgramVariable resultVar, ProgramVariable excVar,
                                     Map<LocationVariable, LocationVariable> atPreVars,
                                     Map<LocationVariable, Term> atPres) {
        this (selfVar, paramVars, resultVar, excVar, atPreVars, atPres, null, null);
    }

    public ProgramVariableCollection(ProgramVariable selfVar,
                                     ImmutableList<ProgramVariable> paramVars,
                                     ProgramVariable resultVar, ProgramVariable excVar,
                                     Map<LocationVariable, LocationVariable> atPreVars,
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

    public ProgramVariableCollection() {
    }
}