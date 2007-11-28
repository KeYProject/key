// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof.init;

import java.util.Map;

import de.uka.ilkd.key.casetool.ModelMethod;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.ListOfProgramVariable;
import de.uka.ilkd.key.logic.op.Op;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.speclang.ListOfClassInvariant;
import de.uka.ilkd.key.speclang.SLTranslationError;


/**
 * The "PreservesThroughout" proof obligation. 
 */
public class PreservesThroughoutPO extends EnsuresPO {
    
    private ListOfClassInvariant invs;
    
    public PreservesThroughoutPO(ModelMethod modelMethod, 
                                 ListOfClassInvariant invs,
                                 InvariantSelectionStrategy invStrategy) {
        super("PreservesThroughout", 
              modelMethod, 
              Op.TOUT,
              invStrategy,
              true);
        this.invs = invs;
    }
    
    
    protected Term getPreTerm(ProgramVariable selfVar, 
                              ListOfProgramVariable paramVars, 
                              ProgramVariable resultVar,
                              ProgramVariable exceptionVar,
                              Map atPreFunctions) {
        return tb.tt();
    }
    
    
    protected Term getPostTerm(ProgramVariable selfVar, 
                               ListOfProgramVariable paramVars, 
                               ProgramVariable resultVar,
                               ProgramVariable exceptionVar,
                               Map atPreFunctions) throws SLTranslationError {        
        return translateInvs(invs);
    }
}
