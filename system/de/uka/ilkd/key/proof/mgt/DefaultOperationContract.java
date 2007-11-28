// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.proof.mgt;

import java.util.HashMap;
import java.util.Map;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.statement.CatchAllStatement;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.Proof;

/**
 * @deprecated
 */
public abstract class DefaultOperationContract extends AbstractContract
        implements OldOperationContract, HoareTripleContract {
    
    protected abstract Term getAdditionalAxioms();
    
    public InstantiatedMethodContract instantiate(MethodContractInstantiation insts, 
            Proof proof, ExecutionContext ec) {
        
        final Services services = proof.getServices();
        
        final Namespace localFunctions   = new Namespace();
        final Namespace localProgramVariables = new Namespace();
        final Map replacementMap = new HashMap();
        
        instantiateMethodParameters(insts, replacementMap, 
                localFunctions, localProgramVariables);
        
        instantiateMethodReceiver(insts, replacementMap, 
                localFunctions, localProgramVariables);
        
        instantiateMethodReturnVariable(insts, replacementMap, 
                localFunctions, localProgramVariables);
        
        instantiateMemoryScope(replacementMap, ec, services);
       
        final ProgramVariable excVar = 
            instantiateCatchAllStatement(getCatchAllStatement(), 
                replacementMap, localFunctions, localProgramVariables, services);        

        instantiateAtPreSymbols(replacementMap, localFunctions, localProgramVariables);
        
        instantiateAuxiliarySymbols(replacementMap, localFunctions, localProgramVariables, proof.getServices());
        return InstantiatedMethodContract.create
            (replacementMap, getPre(), getPost(), getWorkingSpace(), 
             getAdditionalAxioms(), getModifies(), insts.getModality(), excVar, 
             localFunctions, localProgramVariables);
    }
    
    public abstract CatchAllStatement getCatchAllStatement(); 

    
    protected abstract void instantiateAuxiliarySymbols(Map replacementMap, 
            Namespace localFunctions, Namespace localProgramVariables, Services services);
    
    /**
     * @param insts
     * @param replacementMap
     * @param localProgramVariables
     * @param localFunctions
     */
    protected abstract void instantiateMethodReturnVariable(
            MethodContractInstantiation insts, Map replacementMap,
            Namespace localFunctions, Namespace localProgramVariables);

    /**
     * @param localProgramVariables
     * @param replacementMap
     * @param ca
     * @return
     */
    protected ProgramVariable instantiateCatchAllStatement(CatchAllStatement ca,
            Map replacementMap, Namespace localFunctions,
            Namespace localProgramVariables, Services services) {

        ProgramVariable excVar = null;
        if (ca != null) {
            final ProgramVariable paramPV = (ProgramVariable) ca
                    .getParameterDeclaration().getVariableSpecification()
                    .getProgramVariable();

            final ProgramElementName catchAllInstantiadParameterName = services
                    .getVariableNamer().getTemporaryNameProposal(
                            paramPV.name().toString());

            excVar = new LocationVariable(catchAllInstantiadParameterName,
                    paramPV.getKeYJavaType());
            replacementMap.put(paramPV, excVar);
            localProgramVariables.add(excVar);
        }
        return excVar;
    }
    
    /**
     * @param insts
     * @param replacementMap
     * @param localProgramVariables
     * @param localFunctions
     */
    protected abstract void instantiateMethodReceiver(
            MethodContractInstantiation insts, Map replacementMap,
            Namespace localFunctions, Namespace localProgramVariables);

    /**
     * @param insts
     * @param replacementMap
     * @param localProgramVariables
     * @param localFunctions
     */
    protected abstract void instantiateMethodParameters(
            MethodContractInstantiation insts, Map replacementMap,
            Namespace localFunctions, Namespace localProgramVariables);

    protected abstract void instantiateAtPreSymbols(Map replacementMap,
            Namespace localFunctions, Namespace localProgramVariables);
    
    protected void instantiateMemoryScope(Map replacementMap,
            ExecutionContext ec, Services services){
        replacementMap.put(services.getJavaInfo().getDefaultMemoryArea(), ec.getMemoryArea());
    }
    
    public Term getWorkingSpace(){
        return null;
    }
}
