// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//


package de.uka.ilkd.key.rule.soundness;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.inst.SVInstantiations;



public interface RawProgramVariablePrefixes {

    ImmutableList<IProgramVariable>  getFreeProgramVariables ();
    ImmutableList<SchemaVariable>    getFreeSchemaVariables  ();
    ImmutableList<SchemaVariable>    getBoundSchemaVariables ();

    ImmutableList<IProgramVariable>  getPrefix   ( SchemaVariable p );

    ProgramVariablePrefixes instantiate ( SVInstantiations p );

}
