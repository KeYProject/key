// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License.
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof.init;

import java.util.Map;

import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.java.recoderext.ImplicitFieldAdder;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.speclang.ClassInvariant;
import de.uka.ilkd.key.speclang.OperationContract;


/**
 * The "EnsuresPost" proof obligation.
 */
public class EnsuresPostPO extends EnsuresPO {
    
    protected final OperationContract contract;
    
    public EnsuresPostPO(InitConfig initConfig, 
                         String name,
                         OperationContract contract,
                         ImmutableSet<ClassInvariant> assumedInvs) {
        super(initConfig,
              name,
              contract.getProgramMethod(),
              contract.getModality(),
              assumedInvs,
              true);
        this.contract = contract;
    }


    public EnsuresPostPO(InitConfig initConfig, OperationContract contract,
            ImmutableSet<ClassInvariant> assumedInvs) {
        this(initConfig,
             "EnsuresPost ("
                 + contract.getProgramMethod() + ", "
                 + contract.getDisplayName() + ")",
             contract,
             assumedInvs);
    }
    
    protected Term buildGeneralMemoryAssumption(ProgramVariable selfVar,
            ImmutableList<ProgramVariable> paramVars) 
        throws ProofInputException {
	if(!(ProofSettings.DEFAULT_SETTINGS.getProfile() instanceof PercProfile || 
	     ProofSettings.DEFAULT_SETTINGS.getProfile() instanceof RTSJProfile)){
	    return TB.tt();
	}
        Term result = TB.tt();
        Term t_mem = null;

	final ProgramVariable stack = services.getJavaInfo().getAttribute(
					     "stack", "javax.realtime.MemoryArea");
	ProgramVariable initialMemoryArea = services.getJavaInfo().getDefaultMemoryArea();
	t_mem = TB.var(initialMemoryArea);
	result = TB.and(result, TB.not(TB.equals(TB.dot(t_mem,stack), TB.NULL(services))));
	    
	Term initialMemCreatedAndNotNullTerm
	    = CreatedAttributeTermFactory.INSTANCE.createCreatedAndNotNullTerm(services, t_mem);
	result = TB.and(result, initialMemCreatedAndNotNullTerm);
	        
        Term workingSpace=null;
        final ProgramVariable size = services.getJavaInfo().getAttribute(
                "size", "javax.realtime.MemoryArea");
        final ProgramVariable consumed = services.getJavaInfo().getAttribute(
                "consumed", "javax.realtime.MemoryArea");
        Function add = (Function) services.getNamespaces().functions().lookup(new Name("add"));
        Function leq = (Function) services.getNamespaces().functions().lookup(new Name("leq")); 
        
        if(ProofSettings.DEFAULT_SETTINGS.getProfile() instanceof PercProfile){
            workingSpace = contract.getCallerWorkingSpace(selfVar, toPV(paramVars), services);
//            workingSpace = TB.var(services.getJavaInfo().
//                    getAttribute(ImplicitFieldAdder.IMPLICIT_SIZE, contract.getProgramMethod().getKeYJavaType()));
        }else if(contract.getWorkingSpace(selfVar, toPV(paramVars), services)!=null){
            workingSpace = contract.getWorkingSpace(selfVar, toPV(paramVars), services);
            if(contract.getProgramMethod().getMethodDeclaration().externallyConstructedScope()){
                workingSpace = TB.func(add, workingSpace, 
                        contract.getConstructedWorkingSpace(selfVar, toPV(paramVars), services));
            }
        }
        if(workingSpace!=null){
            result = TB.and(result, TB.func(leq, TB.func(add, TB.dot(t_mem,consumed), 
                    workingSpace), TB.dot(t_mem, size)));
        }
        
        if(ProofSettings.DEFAULT_SETTINGS.getProfile() instanceof PercProfile){
            if( !contract.getProgramMethod().isStatic()){
                final ProgramVariable reentrantScope = services.getJavaInfo().getAttribute(
                        ImplicitFieldAdder.IMPLICIT_REENTRANT_SCOPE, services.getJavaInfo().getJavaLangObject());
                Term reentrantWorkingSpace = contract.getReentrantWorkingSpace(selfVar, toPV(paramVars), services);
                Term reentCons = TB.dot(TB.dot(TB.var(selfVar), reentrantScope), consumed);
                Term reentSize = TB.dot(TB.dot(TB.var(selfVar), reentrantScope), size);
                result = TB.and(result, TB.func(leq, TB.func(add, reentCons, 
                        reentrantWorkingSpace), reentSize));
            }

        }

        return result;
    }
    
    
    protected Term getPreTerm(ProgramVariable selfVar,
                              ImmutableList<ProgramVariable> paramVars,
                              ProgramVariable resultVar,
                              ProgramVariable exceptionVar,
                              Map<Operator, Function/*atPre*/> atPreFunctions)
            throws ProofInputException {
        Term result = translatePre(contract, selfVar, toPV(paramVars));
        return result;
    }


    protected Term getPostTerm(ProgramVariable selfVar,
                               ImmutableList<ProgramVariable> paramVars,
                               ProgramVariable resultVar,
                               ProgramVariable exceptionVar,
                               Map<Operator, Function/*atPre*/> atPreFunctions)
            throws ProofInputException {
        Term result = translatePost(contract,
                                    selfVar,
                                    toPV(paramVars),
                                    resultVar,
                                    exceptionVar,
                                    atPreFunctions);

        return result;
    }


    public boolean implies(ProofOblInput po) {
        if(!(po instanceof EnsuresPostPO)) {
            return false;
        }
        EnsuresPostPO epPO = (EnsuresPostPO) po;
        return specRepos.splitContract(epPO.contract)
                        .subset(specRepos.splitContract(contract))
               && assumedInvs.subset(epPO.assumedInvs);
    }


    public boolean equals(Object o) {
        if(!(o instanceof EnsuresPostPO)) {
            return false;
        }
        EnsuresPostPO po = (EnsuresPostPO) o;
        return super.equals(po)
               && contract.equals(po.contract);
    }


    public int hashCode() {
        return super.hashCode() + contract.hashCode();
    }
}
