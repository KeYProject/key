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
        if (newHeap == null) {
            throw new IllegalArgumentException("newHeap can't be null");
        }
        if (!newHeap.sort().equals(services.getTypeConverter().getHeapLDT().targetSort())) {
            throw new IllegalArgumentException("newHeap has to be a heap");
        }
        put(services.getTermBuilder().getBaseHeap(), newHeap);
    }

    @Override
    protected Term convert(ProgramVariable variable, TermServices services) {
        return services.getTermBuilder().var(variable);
    }

}
