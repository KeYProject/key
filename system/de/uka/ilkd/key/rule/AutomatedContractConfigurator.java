package de.uka.ilkd.key.rule;

import java.util.Iterator;

import de.uka.ilkd.key.logic.op.ListOfProgramMethod;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.proof.mgt.ContractSet;
import de.uka.ilkd.key.proof.mgt.DLMethodContract;
import de.uka.ilkd.key.proof.mgt.OldOperationContract;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.speclang.ListOfClassInvariant;
import de.uka.ilkd.key.speclang.SLListOfClassInvariant;

public class AutomatedContractConfigurator implements ContractConfigurator {

    public final static AutomatedContractConfigurator INSTANCE 
        = new AutomatedContractConfigurator();
    
    
    private SpecificationRepository repos;
    private ListOfProgramMethod programMethods;
    private OldOperationContract result;
    private Modality modality;
    
    private AutomatedContractConfigurator() {}
    
    public void setSpecification(SpecificationRepository repos) {
        this.repos = repos;
    }

    public void start() {
        ContractSet ctSet = repos.getContracts(programMethods, modality);
        Iterator it = ctSet.iterator();
        while (it.hasNext()) {
            OldOperationContract ct = (OldOperationContract) it.next();
            if (ct instanceof DLMethodContract) {
                result = ct;
                return;
            }
        }
        if (ctSet.size()>0) {
            result = (OldOperationContract) ctSet.iterator().next();
            return;
        }
        result = null;
    }

    public OldOperationContract getMethodContract() {
        return result;
    }

    public ListOfClassInvariant getPreInvariants() {
        return SLListOfClassInvariant.EMPTY_LIST;
    }

    public ListOfClassInvariant getPostInvariants() {
        return SLListOfClassInvariant.EMPTY_LIST;
    }

    public void setProgramMethods(ListOfProgramMethod pm) {
        this.programMethods = pm;
    }

    public void setModality(Modality modality) {
        this.modality = modality;
    }

    public boolean wasSuccessful() {
        return (result!=null);
    }
    
    public void clear() {
        result=null;        
    }
    
    public void allowConfiguration(boolean allowConfig) {
        // no effect currently, we do not configure anyway
    }

}
