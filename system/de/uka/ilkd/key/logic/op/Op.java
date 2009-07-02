// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.util.Debug;


/** 
 * This class contains logical connectives, most of them derive
 * from this class. If you want to create a term with a connective
 * that is stored in this class you have to take this one, because
 * these operators are handled as singleton so that e.g. 
 * these operators are compared using equality on references not on
 * names. 
 */
public abstract class Op implements Operator {
    
    /** the ususal 'forall' operator 'all' (be A a formula then       
     * 'all x.A' is true if and only if for all elements d of the
     * universe A{x<-d} (x substitued with d) is true */     
    public static final Quantifier ALL = new Quantifier(new Name("all"));
    
    /** the ususal 'exists' operator 'ex' (be A a formula then       
     * 'ex x.A' is true if and only if there is at least one elements
     * d of the universe such that A{x<-d} (x substitued with d) is true */     
    public static final Quantifier EX = new Quantifier(new Name("exist"));
    
    /** the diamond operator of dynamic logic. A formula
     * <alpha;>Phi can be read as after processing the program alpha
     * there exists a state such that Phi holds. */    
    public static final Modality DIA = new Modality(new Name("diamond"));
    
    /** the box operator of dynamic logic. A formula
     * [alpha;]Phi can be read as 'In all states reachable
     * processing the program alpha the formula Phi holds'.*/
    public static final Modality BOX = new Modality(new Name("box"));
    
    /** the wary substitution operator {var<-term}'. {x<-d}'A(x) means
     * replace all free occurrences of variable x in A with d, however
     * without replacing x with a non-rigid A below modalities */
    public static final SubstOp SUBST = new WarySubstOp(new Name("subst"));

    /** the null pointer */
    public static final Function NULL = new RigidFunction(new Name("null"),
						     Sort.NULL, 
						     new Sort[0]);

    /** the 'if-then-else' operator */
    public static final IfThenElse IF_THEN_ELSE = new IfThenElse ();

    /** the 'ifEx-then-else' operator */
    public static final IfExThenElse IF_EX_THEN_ELSE = new IfExThenElse ();

    /** the sum operator */
    public static final NumericalQuantifier SUM = new NumericalQuantifier(new Name("\\sum"));
    
    /** the bounded sum operator */
    public static final BoundedNumericalQuantifier BSUM = new BoundedNumericalQuantifier(new Name("\\bSum"));
    
    /** the product operator */
    public static final NumericalQuantifier PRODUCT = new NumericalQuantifier(new Name("\\product"));
    
    private final Name name;
    
    private final int arity;
   	
    
    protected Op(Name name, int arity) {
	this.name = name;
	this.arity = arity;
    }
    
    /**
     * Returns a modality corresponding to a string
     * @param str name of the modality to return
     */
    public static Modality getModality(String str) {
	return (Modality)Modality.getNameMap().get(str);
    }


    @Override
    public final Name name() {
	return name;
    }
    
    @Override
    public final int arity() {
        return arity;
    }


    /**
     * @return true if the value of "term" having this operator as
     * top-level operator and may not be changed by modalities
     */
    @Override
    public boolean isRigid () {
	return true;
    }
        
    /** 
     * implements the default operator matching rule which means 
     * that the compared object have to be equal otherwise
     * matching fails
     */
    @Override
    public MatchConditions match(SVSubstitute subst, MatchConditions mc,
            Services services) {
        if (subst == this) {
            return mc;
        }
        Debug.out("FAILED. Operators are different(template, candidate)", this, subst);
        return null;
    }
    
    
    @Override
    public String toString() {
	return name().toString();
    }
}
