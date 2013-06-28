package de.uka.ilkd.key.proof.init;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.speclang.WellDefinednessCheck;
import de.uka.ilkd.key.util.Triple;

public class WellDefinednessPO extends AbstractPO implements ContractPO {

    protected static final TermBuilder TB = TermBuilder.DF;

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

    @Override
    public void readProblem() throws ProofInputException {
        final IProgramMethod pm = getProgramMethod();
        // TODO: Build problem here
        Triple<Term, ImmutableList<Term>, Term> po = check.createPOTerm();
        ImmutableList<Term> c = ImmutableSLList.<Term>nil();
        for (Term t: po.second) {
            c = c.append(wd(t));
        }
        Term poTerms = TB.and(wd(po.first),
                              TB.imp(po.first,
                                      TB.and(TB.and(c),
                                              wd(po.third))));
        assignPOTerms(poTerms);
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

    /**
     * Returns the base heap.
     * @return The {@link LocationVariable} which contains the base heap.
     */
    private LocationVariable getHeap() {
       return services.getTypeConverter().getHeapLDT().getHeap();
    }

    private Term wd(Term t) {
        return TB.wd(t);
    }

    @Deprecated
    public Term getMbyAtPre() {
        return null;
    }

}
