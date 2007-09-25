// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.asmkey.logic;


import java.util.*;

import de.uka.ilkd.asmkey.gui.ProverFrame;
import de.uka.ilkd.asmkey.proof.AsmProof;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.inst.SVInstantiations;


/** Meta operator for inlining derived symbols. This meta operator
 * replaces a derived symbol invocation with the definition of the
 * derived symbol and substitutes the formal parameters with the
 * arguments of the invocation.
 *
 * @author Hubert Schmid
 * @author Stanislas Nanchen
 */
public final class MetaDerived extends AsmMetaOperator {
    
    /** Short reference to TermFactory. */
    private static final TermFactory tf = AsmTermFactory.DEFAULT; 

    /** constructs a new meta operator. Only one instance is required,
     * so this may be a singleton class. */
    public MetaDerived() {
        super("Base.#META_DERIVED", null,
              new Sort[] { null });
    }


    /** Returns the body of the derived symbol with parameter substitution
     * already performed; in addition, it does the big operator substitution
     * in the special case of derived predicates. 'term' contains one subterm -- the derived
     * symbol invocation.  The derived symbol is determined by the operator
     * of this subterm. */
    public Term calculate(Term term, SVInstantiations svInst) {
        Term call = term.sub(0);
	Term result;
	/**
	 * we have two main cases:
	 * - derived functions/rules : straight forward subsitutition.
	 * - derived predicates : first substitution; then expansion.
	 */
	Operator op = call.op();
	if (op instanceof DerivedFunction) {
	    DerivedFunction df = (DerivedFunction) call.op();
	    FormalParameter[] params = df.formalParameters();
	    if (call.arity() != params.length) {
		throw new RuntimeException
		    ("Derived function call und derived symbol have different arities.");
	    }
	    Map map = new HashMap();
	    for (int i = 0; i < params.length; ++i) {
		map.put(params[i], call.sub(i));
	    }
	    result = FormalParameterSubstitution.apply(map, df.body());
	    if (call.sort() == Sort.FORMULA) {
		result = expandBigOperator(result, svInst);
	    }
	    return result;
	} else {
	    return call;
	}
    }

    /**
     * For derived predicates: it does the expansion of the big operators, in
     * a recursive fashion.
     */
    private Term expandBigOperator(Term term, SVInstantiations svInst) {
	Transformator trans = new Transformator(getNonRigidFunctions());

	return trans.compute(term);
    }

    private class Transformator {

	private final NonRigidFunction[] dynamics;
	private boolean alreadyOneBig = false;
	
	public Transformator(NonRigidFunction[] dynamics) {
	    this.dynamics = dynamics;
	}

	public Term compute(Term term) {
	    return transform(term, new EnvStack());
	}
	
	private Term transform(Term term, EnvStack stack) {
	    Term[] subterms = new Term[term.op().arity()];
	    Operator op = term.op();
	    Term result;
	    boolean isNew;
	    
	    /* We are not at the end of the tree and must recursively
	     * go down.
	     */
	    if (op instanceof BigOperator) {
		/* we must expand  and each time load the stack with transformation
		 * info on the stack. */
		if (alreadyOneBig) {
		    throw new IllegalStateException
			("Due to limitations of KeY, it is not possible to have " +
			 "big operators 'l'un dans l'autre'.");
		} else {
		    result = expand(term, stack);
		    alreadyOneBig = true;
		}
	    } else if (op instanceof NArityFunction) {
		/* We have the NArityFunction, it can only
		 * have %x as argument. we can substitute with the
		 * "f" term as given by the stack.
		 */
		result = stack.getFTerm((NArityFunction) op);
	    } else {
		isNew = false;
		for(int i=0; i<subterms.length; i++) {
		    subterms[i] = transform(term.sub(i), stack);
		    isNew = isNew | (subterms[i] != term.sub(i));
		}
		
		ArrayOfQuantifiableVariable vars = term.varsBoundHere(0);
		boolean vars_has_ok_size = vars.size() == 1;
		if ((op == Op.ALL || op == Op.EX) &&
		    vars_has_ok_size &&
		    vars.getQuantifiableVariable(0) instanceof NArityLogicVariable) {
		    /* if we have our found a NArityLogicVariable var, we must
		     * make the remplacement.
		     */
		    LogicVariable[] xs = stack.getLogicVariables
			((NArityLogicVariable) vars.getQuantifiableVariable(0));
		    result = subterms[0];
		    for (int i = xs.length - 1; i >= 0; i--) {
			result = tf.createQuantifierTerm((Quantifier) op, xs[i], result);
		    }
		} else if ((op == Op.ALL || op == Op.EX) &&
			   vars_has_ok_size &&
			   vars.getQuantifiableVariable(0).sort() == Sort.ANY) {
		    // we must create a variable of same name with the "correct" sort.
		    LogicVariable x = new LogicVariable
			(vars.getQuantifiableVariable(0).name(),
			 stack.getFSort(vars.getQuantifiableVariable(0).sort()));
		    result = tf.createQuantifierTerm((Quantifier) op, x, subterms[0]);
		} else if (op instanceof LogicVariable &&
			   term.sort() == Sort.ANY) {
		    LogicVariable x = new LogicVariable(op.name(),
							stack.getFSort(term.sort()));
		    result = tf.createVariableTerm(x);
		} else {
		    /* we can simply reconstitute */
		    if (isNew) {
			result = tf.createTerm(op,
					       subterms,
					       op.arity()==0?Term.EMPTY_VAR_LIST:term.varsBoundHere(0),
					       term.javaBlock());
		    } else {
			/* nothing has changed, no need to construct a new term */
			return term;
		    }
		}
	    }
	    
	    return result;
	}
	
	private Term expand(Term term, EnvStack stack) {
	    BigOperator op = (BigOperator) term.op();
	    if (dynamics.length == 0) {
		return op.base();
	    } else {
		Term main = term.sub(0);
		if (dynamics.length == 1) {
		    return single_expand(main, stack, dynamics[0], op);
		} else {
		    int last = dynamics.length - 1;
		    Term result = op.join(single_expand(main, stack, dynamics[last-1], op),
					  single_expand(main, stack, dynamics[last], op));
		    for(int i = last-2; i>=0; i--) {
			result = op.join(single_expand(main, stack, dynamics[i], op),
					 result);
		    }
		    return result;
		}
	    }
	}
	
	private Term single_expand(Term main,
				   EnvStack stack,
				   NonRigidFunction f,
				   BigOperator op) {
	    LogicVariable[] xs = new LogicVariable[f.arity()];
	    Term[] terms = new Term[f.arity()];
	    Term fterm;
	    VariableFactory factory = new VariableFactory();
	    Sort fsort;
	    StackItem item;
	    for(int j = 0; j < xs.length; j++) {
		xs[j] = factory.createNewVariable(main, op.variableBase(), f.argSort(j));
		terms[j] = tf.createVariableTerm(xs[j]);
	    }
	    fterm = tf.createFunctionTerm(f, terms);
	    fsort = fterm.sort();
	    item = new StackItem(op.nArityFunction(), fterm,
				 op.nArityVariable(), xs,
				 op.genericSort(), fsort);
	    stack.push(item);
	    Term result = transform(main, stack);
	    stack.pop();
	    return result;
	}
    }

    static class StackItem {
	public NArityFunction function;
	public NArityLogicVariable variable;
	public Sort gsort;
	
	public Term fterm;
	public LogicVariable[] xs;
	public Sort fsort;

	public StackItem(NArityFunction function,
			 Term fterm,
			 NArityLogicVariable variable,
			 LogicVariable[] xs,
			 Sort gsort,
			 Sort fsort) {
	    this.function = function;
	    this.variable = variable;
	    this.gsort = gsort;

	    this.fterm = fterm;
	    this.xs = xs;
	    this.fsort = fsort;
	}
    }

    static abstract class Selector {
	public abstract Object key(StackItem item);
	public abstract Object result(StackItem item);
	public abstract String kind();
    }
    
    static class EnvStack {
	
	private LinkedList stack;
	
	public EnvStack() {
	    stack = new LinkedList();
	}
	
	public void push(StackItem trans) {
	    stack.addFirst(trans);
	}
	
	public StackItem pop() {
	    return (StackItem) stack.removeFirst();
	}

	private Object getFromStack(Object key, Selector selector) {
	    Object result = null;
	    ListIterator it = stack.listIterator();
	    while (it.hasNext()) {
		StackItem item = (StackItem) it.next();
		if (selector.key(item) == key) {
		    result = selector.result(item);
		}
	    }
	    if (result == null) {
		throw new NoSuchElementException("MetaDerived:The stack contains no such "
						 + selector.kind() + ":" + key);
	    } else {
		return result;
	    }
	}
 	
	public Term getFTerm(NArityFunction function) {
	    return (Term) getFromStack
		(function,
		 new Selector() {
		     public Object key(StackItem item) { return item.function; }
		     public Object result(StackItem item) { return item.fterm; }
		     public String kind() { return "kind"; }
		 });
	}
	
	public LogicVariable[] getLogicVariables(NArityLogicVariable var) {
	    return (LogicVariable[]) getFromStack
		(var,
		 new Selector() {
		     public Object key(StackItem item) { return item.variable; }
		     public Object result(StackItem item) { return item.xs; }
		     public String kind() { return "NArityLogicVariable"; }
		 });
	}
	
	public Sort getFSort(Sort sort) {
	    return (Sort) getFromStack
		(sort,
		 new Selector() {
		     public Object key(StackItem item) { return item.gsort; }
		     public Object result(StackItem item) { return item.fsort; }
		     public String kind() { return "sort"; }
		 });
	}
    }


    /** static function to retrieve the dynamic functions. */
    public NonRigidFunction[] getNonRigidFunctions() {
	AsmProof proof;
	try {
	    return ((AsmProof) ProverFrame.getInstance().mediator().getProof()).getNonRigidFunctions();
	} catch (ClassCastException e) {
	    throw new IllegalStateException
		("AsmKeY is required. You may not use the MetaDerived in KeY.");
	}
    }
}


