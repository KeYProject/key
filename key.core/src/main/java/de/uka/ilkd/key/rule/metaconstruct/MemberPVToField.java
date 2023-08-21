/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.AbstractTermTransformer;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.rule.inst.SVInstantiations;



public final class MemberPVToField extends AbstractTermTransformer {

    public MemberPVToField() {
        super(new Name("#memberPVToField"), 1);
    }


    @Override
    public Term transform(Term term, SVInstantiations svInst, Services services) {
        HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();


        Operator op = term.sub(0).op();
        if (op instanceof LocationVariable) {
            LocationVariable fieldPV = (LocationVariable) op;
            Function fieldSymbol = heapLDT.getFieldSymbolForPV(fieldPV, services);
            return services.getTermBuilder().func(fieldSymbol);
        } else if (heapLDT.getSortOfSelect(op) != null) {
            return term.sub(0).sub(2);
        } else {
            assert false;
            return null;
        }
    }
}
