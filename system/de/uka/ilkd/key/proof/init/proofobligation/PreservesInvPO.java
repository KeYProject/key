// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.

package de.uka.ilkd.key.proof.init.proofobligation;

import java.util.Map;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.speclang.ClassInvariant;


/**
 * The "PreservesInv" proof obligation.
 */
public class PreservesInvPO extends EnsuresPO {

    private final ImmutableSet<ClassInvariant> ensuredInvs;


    protected PreservesInvPO(InitConfig initConfig,
	    		     String name,
                             ProgramMethod programMethod,
                             ImmutableSet<ClassInvariant> assumedInvs,
                             ImmutableSet<ClassInvariant> ensuredInvs) {
        super(initConfig, name, programMethod, Op.BOX, assumedInvs, false);
        this.ensuredInvs = ensuredInvs;
    }


    PreservesInvPO(InitConfig initConfig,
	    		  ProgramMethod programMethod,
                          ImmutableSet<ClassInvariant> assumedInvs,
                          ImmutableSet<ClassInvariant> ensuredInvs) {
        this(initConfig,
             "PreservesInv (" + programMethod + ")",
             programMethod,
             assumedInvs,
             ensuredInvs);
    }


    protected Term getPreTerm(ProgramVariable selfVar,
                              ImmutableList<ProgramVariable> paramVars,
                              ProgramVariable resultVar,
                              ProgramVariable exceptionVar,
                              Map<Operator, Function/*atPre*/> atPreFunctions) throws ProofInputException {
        return TB.tt();
    }


    protected Term getPostTerm(ProgramVariable selfVar,
                               ImmutableList<ProgramVariable> paramVars,
                               ProgramVariable resultVar,
                               ProgramVariable exceptionVar,
                               Map<Operator, Function/*atPre*/> atPreFunctions) throws ProofInputException {
        return translateInvs(ensuredInvs);
    }


    public boolean implies(ProofOblInput po) {
        if(!(po instanceof PreservesInvPO)) {
            return false;
        }
        PreservesInvPO piPO = (PreservesInvPO) po;
        return programMethod.equals(piPO.programMethod)
        	&& modality.equals(piPO.modality)
        	&& piPO.ensuredInvs.subset(ensuredInvs)
                && assumedInvs.subset(piPO.assumedInvs);
    }


    public boolean equals(Object o) {
        if(!(o instanceof PreservesInvPO)) {
            return false;
        }
        PreservesInvPO po = (PreservesInvPO) o;
        return super.equals(po)
               && ensuredInvs.equals(po.ensuredInvs);
    }
    

    public ImmutableSet<ClassInvariant> getInvs() {
        return ensuredInvs;
    }


    public int hashCode() {
        return super.hashCode() + ensuredInvs.hashCode();
    }
}
