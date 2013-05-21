package de.uka.ilkd.key.proof.init;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.speclang.WellDefinednessCheck;

public class WellDefinednessPO extends AbstractPO implements ContractPO {

    public WellDefinednessPO(InitConfig initConfig, WellDefinednessCheck check) {
        super(initConfig, check.getName());
        // TODO Auto-generated constructor stub
    }

    private WellDefinednessCheck check;

    @Override
    public void readProblem() throws ProofInputException {
        // TODO Auto-generated method stub

    }

    @Override
    public boolean implies(ProofOblInput po) {
        // TODO Auto-generated method stub
        return false;
    }

    @Override
    public WellDefinednessCheck getContract() {
        return check;
    }

    @Deprecated
    public Term getMbyAtPre() {
        return null;
    }

}
