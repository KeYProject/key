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

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.Op;
import de.uka.ilkd.key.logic.sort.Sort;

/** This class represents the bigand and bigor operators
 * for expressing a property over all function, dynamic or
 * not and with access or update properties.
 *
 * @author Stanislas Nanchen 
 */

public abstract class BigOperator extends AsmOp {

    /** Short refernce to TermFactory. */
    private static final TermFactory tf = AsmTermFactory.DEFAULT; 

    private NArityLogicVariable var;
    private NArityFunction function;
    private Sort gsort;

    public static BigOperator bigAnd(final Name id,
				     NArityLogicVariable var, NArityFunction function, Sort sort) {
	return new BigOperator(new Name("And"), Sort.FORMULA, new Sort[] {Sort.FORMULA},
			       var, function, sort) {

		public Term base() {
		    return tf.createJunctorTerm(Op.TRUE);
		}
		
		public Term join(Term term1, Term term2) {
		    return tf.createJunctorTerm(Op.AND, term1, term2);
		}

	    };
    }

    public static BigOperator bigOr(final Name func,
				    NArityLogicVariable var, NArityFunction function, Sort sort) {
	return new BigOperator(new Name("Or"), Sort.FORMULA, new Sort[] {Sort.FORMULA},
			       var, function, sort) {
		
		public Term base() {
		    return tf.createJunctorTerm(Op.FALSE);
		}
		
		public Term join(Term term1, Term term2) {
		    return tf.createJunctorTerm(Op.OR, term1, term2);
		}

	    };
    }

    private BigOperator(Name name, Sort sort, Sort[] args,
			NArityLogicVariable var, NArityFunction function, Sort gsort) {
	super(name, sort, args);
	this.var = var;
	this.function = function;
	this.gsort = gsort;
    }

    public NArityLogicVariable nArityVariable() {
	return var;
    }

    public NArityFunction nArityFunction() {
	return function;
    }
    
    public Sort genericSort() {
	return gsort;
    }

    public abstract Term base();

    /** Used for computing the result of the metaoperator {@link MetaBigOperator}*/
    public abstract Term join(Term term1, Term term2);


    /** the name used for the NArityLogicVariable */
    public Name getVariableName() {
    	return var.name();
    }

    public String variableBase() {
	return var.name().toString();
    }

    
}
