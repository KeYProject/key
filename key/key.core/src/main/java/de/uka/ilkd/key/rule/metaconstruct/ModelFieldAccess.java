package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.AbstractTermTransformer;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

public class ModelFieldAccess extends AbstractTermTransformer {
    public ModelFieldAccess() {
        super(new Name("#modelFieldAccess"), 2);
    }

    @Override
    public Term transform(Term term,
                          SVInstantiations svInst,
                          Services services ) {
        HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();

        LocationVariable heapVar = heapLDT.getHeap();
        Term heap = services.getTermBuilder().var(heapVar);
        Term receiver = term.sub(0);
        Term fieldPV = term.sub(1);
        Function fieldSymbol
                = heapLDT.getFieldSymbolForPV((LocationVariable) fieldPV.op(), services);
        return  services.getTermBuilder().func(fieldSymbol, heap, receiver);
    }
}
