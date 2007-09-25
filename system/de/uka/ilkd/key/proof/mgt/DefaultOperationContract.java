package de.uka.ilkd.key.proof.mgt;

import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.statement.CatchAllStatement;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
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
            Proof proof) {
        
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
       
        final ProgramVariable excVar = 
            instantiateCatchAllStatement(getCatchAllStatement(), 
                replacementMap, localFunctions, localProgramVariables, services);        

        instantiateAtPreSymbols(replacementMap, localFunctions, localProgramVariables);
        
        instantiateAuxiliarySymbols(replacementMap, localFunctions, localProgramVariables, proof.getServices());
        return InstantiatedMethodContract.create
            (services, replacementMap, getPre(), getPost(), getAdditionalAxioms(),
             getModifies(), insts.getModality(), excVar, 
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

}
