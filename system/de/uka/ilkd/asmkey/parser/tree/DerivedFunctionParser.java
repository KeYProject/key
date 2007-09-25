// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.asmkey.parser.tree;

import de.uka.ilkd.asmkey.logic.*;
import de.uka.ilkd.asmkey.parser.env.DeclarationEnvironment;
import de.uka.ilkd.asmkey.parser.env.EnvironmentException;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.parser.ParserException;

/**
 * Instances of this class are responsible for completing
 * the parsing of devired function symbols.
 * it computes the rigid/rec information and replace
 * the intermediary operators with permanent ones.
 */
public class DerivedFunctionParser {

    /** we review the derived function of this environment. */
    protected DeclarationEnvironment env;

    /** a graph to compute the informations */
    protected DerivedGraph graph;

    public DerivedFunctionParser(DeclarationEnvironment env,
				 DerivedGraph graph) {
	this.env = env;
	this.graph = graph;
    }

    public void doAnalysis() {
	populateGraph();
	recordRecursiveInformation();
	recordRigidInformation();
    }

    public void replaceSymbols() throws ParserException {
	IteratorOfDerivedFunction it = graph.iterator();
	ParsingDerivedFunction func;
	DerivedFunction new_func, tmp;
	while(it.hasNext()) {
	    tmp = it.next();
	    if(tmp instanceof ParsingDerivedFunction) {
		func = (ParsingDerivedFunction) tmp;
		if(func.isRigid()) {
		    new_func = new RigidDerivedFunction(func.name(),
							func.sort(),
							func.formalParameters(),
							func.isRecursive());
		} else {
		    new_func = new NonRigidDerivedFunction(func.name(),
							   func.sort(),
							   func.formalParameters(),
							   func.isRecursive());
		}
		try {
		    env.replaceOperator(new_func);
		} catch (EnvironmentException e) {
		    throw new ParserException("Should not happen: " + e.toString(),
					      func.location());
		}
	    }
	}
	it = graph.iterator();
	while(it.hasNext()) {
	    tmp = it.next();
	    if (tmp instanceof ParsingDerivedFunction) {
		func = (ParsingDerivedFunction) tmp;
		try {
		    new_func = (DerivedFunction) env.getOperator(func.name());
		} catch (EnvironmentException ee) {
		    throw new ParserException("New derivered operator "
					      + func.name() +
					      "does not exists:" + ee.toString(),
					      func.location());
		}
		new_func.setBody(substituteInBody(func.body(), func), func.location());
	    }
	}
    }

    public void doPostAnalysis() {

    }

    protected void populateGraph() {
	IteratorOfDerivedFunction it = graph.iterator();
	DerivedFunction func;
	while(it.hasNext()) {
	    func = it.next();
	    if (func instanceof ParsingDerivedFunction) {
		/* go through the body */
		populateGraph(func.body(), (ParsingDerivedFunction) func);
	    }
	}
    }

    private void populateGraph(Term term, ParsingDerivedFunction func) {
	if (term.op() instanceof ParsingDerivedFunction) {
	    graph.addEdge(func, (ParsingDerivedFunction) term.op());
	}
	for(int i=0; i<term.arity(); i++) {
	    populateGraph(term.sub(i), func);
	}
    }

    protected void recordRecursiveInformation() {
	IteratorOfDerivedFunction it = graph.iterator();
	DerivedFunction func;
	while(it.hasNext()) {
	    func = it.next();
	    if(func instanceof ParsingDerivedFunction) {
		((ParsingDerivedFunction)func).setRecursiveFlag(graph.isRecursive(func));
	    }
	}
    }

    protected void recordRigidInformation() {
	RigidInfoAnalysis analysor = new RigidInfoAnalysis(graph);
	analysor.compute();
    }

    private Term substituteInBody(Term term, ParsingDerivedFunction func) throws ParserException {
	Operator op = term.op();
	Term[] sub = new Term[term.arity()];
	for (int i = 0; i<term.arity(); i++) {
	    sub[i] = substituteInBody(term.sub(i), func);
	}
	if (op instanceof ParsingDerivedFunction) {
	    try {
		op = env.getOperator(op.name());
	    }
	    catch (EnvironmentException ee) {
		throw new ParserException("Problem when replacing old derivered operator "
					  + func.name() +
					  "with new derivered operator:" + ee.toString(),
					  func.location());
	    }
	}
	return AsmTermFactory.ASMDEFAULT.createTerm(op, sub,
						    term.varsBoundHere(0),
						    term.executableJavaBlock());
    }
    
    
}
