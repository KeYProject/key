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

import java.util.NoSuchElementException;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.MetaOperator;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.inst.SVInstantiations;


/** Meta operator for ASMs. This abstract class implements the
 * MetaOperator interface. The method calculate() is called each time
 * a taclet with a meta operator is applied. */

public abstract class AsmMetaOperator extends AsmOp implements MetaOperator {

    /** construct a new asm meta operator with the given name, the
     * given sort and the given subterms. */
    AsmMetaOperator(String name, Sort sort, Sort[] args) {
        super(new Name(name), sort, args);
    }

    public final Term calculate(Term term, SVInstantiations svInst, Services services) {
        return calculate(term, svInst);
    }

    /** This method is called each time a taclet with this operator is
     * applied. The top level operator of 'term' is this
     * operator. 'svInst' contains the variable instantiations of the
     * taclet application.  The term returned by this method replaced
     * the given term in the sequent. */
    protected abstract Term calculate(Term term, SVInstantiations svInst);

    public static MetaOperator getMetaOperator(Name name) {
	String id = name.toString();
	if (id.equals("Base.#META_DERIVED")) {
	    return new MetaDerived();
	} else if (id.equals("Base.#OP_EQ_ARGS")) {
	    return new MetaOpEqualArgs(); 
	} else if (id.equals("Base.#ACCT_ARGS")) {
	    return new MetaAccTArgs();
	} else {
	    throw new NoSuchElementException("There is no MetaOperator with name=" + name);
	}
    }
    
    public MetaOperator getParamMetaOperator(String param) {
       return null;
    }


}
