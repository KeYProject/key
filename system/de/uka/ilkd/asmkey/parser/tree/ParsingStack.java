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

import java.util.HashMap;
import java.util.Map;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.op.IteratorOfOperator;
import de.uka.ilkd.key.logic.op.ListOfOperator;
import de.uka.ilkd.key.logic.op.Operator;


/**
 * The parsing stack contains different kind of operators that
 * are added provisorily to the environment:
 * - logical variables;
 * - pseudo-fonctions for big operators;
 * - parameters of a derived function/named rule; 
 */
public class ParsingStack {

    Map stack;

    public ParsingStack() {
	stack = new HashMap();
    }

    public ParsingStack(Map stack) {
	this.stack = stack;
    }

    public ParsingStack(ListOfOperator ops) {
	this();
	pushAll(ops);
    }
    
    public void pushAll(Operator[] ops) {
	for (int i=0; i<ops.length; i++) {
	    stack.put(ops[i].name(), ops[i]);
	}
    }

    public void pushAll(ListOfOperator ops) {
	if (ops != null) {
	    IteratorOfOperator it = ops.iterator();
	    while (it.hasNext()) {
		push(it.next());
	    }
	}
    }

    public void push(Operator op) {
	stack.put(op.name(), op);
    }

    public void pop(Operator op) {
	stack.remove(op.name());
    }

    public boolean contains(Name op) {
	return stack.containsKey(op);
    }
    
    public Operator get(Name op) {
	return (Operator) stack.get(op);
    }

}
