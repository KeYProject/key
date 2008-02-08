package de.uka.ilkd.key.visualdebugger;

import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ModStrategy;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.mgt.Contract;
import de.uka.ilkd.key.proof.mgt.Contractable;

public class WatchpointPO implements ProofOblInput{

    public boolean askUserForEnvironment() {
        // TODO Auto-generated method stub
        return false;
    }

    public Contractable[] getObjectOfContract() {
        // TODO Auto-generated method stub
        return null;
    }

    public ProofAggregate getPO() {
        // TODO Auto-generated method stub
        return null;
    }

    public boolean initContract(Contract ct) {
        // TODO Auto-generated method stub
        return false;
    }

    public String name() {
        // TODO Auto-generated method stub
        return null;
    }

    public void readActivatedChoices() throws ProofInputException {
        // TODO Auto-generated method stub
        
    }

    public void readProblem(ModStrategy mod) throws ProofInputException {
        // TODO Auto-generated method stub
        
    }

    public void readSpecs() {
        // TODO Auto-generated method stub
        
    }

    public void setInitConfig(InitConfig i) {
        // TODO Auto-generated method stub
        
    }

}
