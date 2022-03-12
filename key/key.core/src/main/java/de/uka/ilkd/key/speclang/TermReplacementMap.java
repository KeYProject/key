package de.uka.ilkd.key.speclang;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.ProgramVariable;

/**
 * A replacement map for terms.
 */
public class TermReplacementMap extends ReplacementMap<Term> {

    public TermReplacementMap(TermFactory tf) {
        super(tf);
    }

    public void replaceHeap(final Term newHeap, final Services services) {
        assert newHeap != null;
        assert newHeap.sort().equals(services.getTypeConverter().getHeapLDT().targetSort());
        put(services.getTermBuilder().getBaseHeap(), newHeap);
    }

    @Override
    protected Term convert(ProgramVariable variable, TermServices services) {
        return services.getTermBuilder().var(variable);
    }

}
