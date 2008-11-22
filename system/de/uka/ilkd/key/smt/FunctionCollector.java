package de.uka.ilkd.key.smt;

import java.util.ArrayList;
import java.util.HashMap;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.Visitor;
import de.uka.ilkd.key.logic.op.ArrayOp;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * This class can be used to collect functions of a formula.
 * 
 * @author Simon Greiner
 *
 */
public class FunctionCollector extends Visitor {

    private HashMap<Operator, ArrayList<Sort>> functions = new HashMap<Operator, ArrayList<Sort>>();

    private Services services;

    public FunctionCollector(Services services) {
	this.services = services;
    }

    @Override
    public void visit(Term visited) {
	if (isFunction(visited, this.services)) {
	    addFunction(visited);
	}
    }

    public HashMap<Operator, ArrayList<Sort>> getFoundFunctions() {
	return functions;
    }

    private void addFunction(Term t) {
	if (functions.containsKey(t.op())) {
	    this.updateFunction(t);
	} else {
	    ArrayList<Sort> sorts = new ArrayList<Sort>();
	    for (int i = 0; i < t.arity(); i++) {
		sorts.add(t.sub(i).sort());
	    }
	    sorts.add(t.sort());
	    functions.put(t.op(), sorts);
	}
    }

    private void updateFunction(Term t) {
	ArrayList<Sort> sorts = functions.get(t.op());
	//update the sorts of the arguments
	for (int i = 0; i < t.arity(); i++) {
	    Sort supersort = getSuperSort(t.sub(i).sort(), sorts.get(i));
	    sorts.set(i, supersort);
	}
	//update the result sort
	Sort supersort = getSuperSort(t.sort(), sorts.get(t.arity()));
	sorts.set(t.arity(), supersort);
    }

    private Sort getSuperSort(Sort s1, Sort s2) {
	if (s1.extendsTrans(s2)) {
	    return s2;
	} else if (s2.extendsTrans(s1)) {
	    return s1;
	}
	//TODO add Debug message
	return null;
    }

    private boolean isFunction(Term t, Services services) {
	boolean isFun = false;
	if (t.op() instanceof ArrayOp) {
	    isFun = true;
	} else if (t.op() instanceof Function
		&& !(t.op() == services.getTypeConverter().getIntegerLDT()
			.getAdd()
			|| t.op() == services.getTypeConverter()
				.getIntegerLDT().getSub()
			|| t.op() == services.getTypeConverter()
				.getIntegerLDT().getNeg()
			|| t.op() == services.getTypeConverter()
				.getIntegerLDT().getMul()
			|| t.op() == services.getTypeConverter()
				.getIntegerLDT().getDiv()
			|| t.op() == services.getTypeConverter()
				.getIntegerLDT().getLessThan()
			|| t.op() == services.getTypeConverter()
				.getIntegerLDT().getGreaterThan()
			|| t.op() == services.getTypeConverter()
				.getIntegerLDT().getLessOrEquals()
			|| t.op() == services.getTypeConverter()
				.getIntegerLDT().getGreaterOrEquals() || t.op() == services
			.getTypeConverter().getIntegerLDT().getNumberSymbol())
		&& !(t.sort() == Sort.FORMULA)) {
	    isFun = true;
	}

	return isFun;
    }

}
