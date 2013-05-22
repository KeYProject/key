package de.uka.ilkd.key.proof.init;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.speclang.WellDefinednessCheck;

public class WellDefinednessPO extends AbstractPO implements ContractPO {

    private WellDefinednessCheck check;

    public WellDefinednessPO(InitConfig initConfig, WellDefinednessCheck check) {
        super(initConfig, check.getName());
        this.check = check;
    }

    protected IProgramMethod getProgramMethod() {
        IObserverFunction pm = getContract().getTarget();
        assert pm instanceof IProgramMethod;
        return (IProgramMethod)pm;
     }

    /**
     * Returns the base heap.
     * @return The {@link LocationVariable} which contains the base heap.
     */
    private LocationVariable getBaseHeap() {
       return services.getTypeConverter().getHeapLDT().getHeap();
    }

    @Override
    public void readProblem() throws ProofInputException {
        final IProgramMethod pm = getProgramMethod();
        // TODO: Build problem here
        assignPOTerms(check.getRequires(getBaseHeap()));
    }

    @Override
    public boolean implies(ProofOblInput po) {
        if (!(po instanceof WellDefinednessPO)) {
            return false;
        }
        WellDefinednessPO wPO = (WellDefinednessPO) po;
        return specRepos.getWdChecks(wPO.check.getKJT(), wPO.check.getTarget())
                .subset(specRepos.getWdChecks(check.getKJT(), check.getTarget()));
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
