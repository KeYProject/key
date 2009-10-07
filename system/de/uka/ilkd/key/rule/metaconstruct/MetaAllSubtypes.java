// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
// This file is part of KeY - Integrated Deductive Software Design 
// Copyright (C) 2001-2003 Universitaet Karlsruhe, Germany
//                         and Chalmers University of Technology, Sweden          
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
package de.uka.ilkd.key.rule.metaconstruct;

import java.util.Iterator;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.AbstractMetaOperator;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.TermSymbol;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/** Is used for OCL simplification.
 * Extracts all subtypes of the given class from the 
 * current UML model.
 */
public class MetaAllSubtypes extends AbstractMetaOperator {


    private TermFactory origTf = TermFactory.DEFAULT;

    public MetaAllSubtypes() {
	super(new Name("#allSubtypes"), 1);
    }

    /**
     * checks whether the top level structure of the given @link Term
     * is syntactically valid, given the assumption that the top level
     * operator of the term is the same as this Operator. The
     * assumption that the top level operator and the term are equal
     * is NOT checked.  
     * @return true iff the top level structure of
     * the @link Term is valid.
     */
    public boolean validTopLevel(Term term) {
	return term.arity()==arity();
    }


    /** calculates the resulting term. */
    public Term calculate(Term term, SVInstantiations svInst, Services services) {
	Namespace namespace = services.getNamespaces().functions();

	TermSymbol nil = (TermSymbol)namespace.lookup(new Name("$empty_set"));
	TermSymbol cons = (TermSymbol)namespace.lookup(new Name("$insert_set"));
	Term nilTerm = origTf.createFunctionTerm(nil);

	//Extract the subtypes in form of KeYJavaTypes
	JavaInfo javaInfo = services.getJavaInfo();
	String className = term.sub(0).op().name().toString();
	KeYJavaType keyType 
	    = javaInfo.getKeYJavaTypeByClassName(className);
	ImmutableList<KeYJavaType> subtypes 
	    = javaInfo.getKeYProgModelInfo().getAllSubtypes(keyType);
	subtypes = subtypes.append(keyType);

	//Build replacewith-term
	Iterator<KeYJavaType> iter = subtypes.iterator();
	Term result = nilTerm;
	for (int i=0; iter.hasNext(); i++) {
	    Name theName = new Name(iter.next().getFullName());
	    TermSymbol ts = (Function)namespace.lookup(theName);
	    Term t = origTf.createFunctionTerm(ts);
	    result = origTf.createFunctionTerm(cons, t, result);
	}
	return result;
    }
}
