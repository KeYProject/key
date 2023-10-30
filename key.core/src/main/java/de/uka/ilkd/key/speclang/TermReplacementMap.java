/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.ProgramVariable;

/**
 * A replacement map for terms.
 *
 * @author lanzinger
 */
public class TermReplacementMap extends ReplacementMap<Term> {

    /**
     * constructs a replacement map with the given term factory
     *
     * @param tf a term factory
     */
    public TermReplacementMap(TermFactory tf) {
        super(tf);
    }

    /**
     * adds a replacement of heap with newHeap
     *
     * @param newHeap the heap that should be used
     * @param services services
     */
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
