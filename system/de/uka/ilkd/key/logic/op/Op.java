// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.logic.op;

import java.io.ObjectStreamException;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
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
    
    // OPERATORS
    /** the ususal 'negation' operator '-' */
    public static final Junctor NOT = new Junctor(new Name("not"),1);	
    /** 
     * the ususal 'and' operator '/\' (be A, B formulae then 'A /\ B'
     * is true if and only if A is true and B is true 
     */
    public static final Junctor AND = new Junctor(new Name("and"),2);
    /** 
     * the ususal 'or' operator '\/' (be A, B formulae then 'A \/ B'
     * is true if and only if A is true or B is true 
     */
    public static final Junctor OR = new Junctor(new Name("or"),2);
    /**
     * the ususal 'implication' operator '->' (be A, B formulae then
     * 'A -> B' is true if and only if A is false or B is true 
     */
    public static final Junctor IMP = new Junctor(new Name("imp"),2);
    /** 
     * the ususal 'equivalence' operator '<->' (be A, B formulae then       
     * 'A <->  B' is true if and only if A and B have the same truth
     * value 
     */ 
    public static final Equality EQV = new Equality(new Name("equiv"),
						    Sort.FORMULA);
    /** the ususal 'equality' operator '=' */
    public static final Equality EQUALS = new Equality(new Name("equals"));
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
    /** the throughout operator of dynamic logic. A formula
     * [[alpha;]]Phi can be read as 'In all intermediate states during
     * processing the program alpha the formula Phi holds'.*/
    public static final Modality TOUT = new Modality(new Name("throughout"));
    /**
     * Diamond operator used for a transaction that is going to commit 
     */
    public static final Modality DIATRC = new Modality(new Name("diamond_trc"));
    /**
     * Box operator used for a transaction that is going to commit 
     */
    public static final Modality BOXTRC = new Modality(new Name("box_trc"));
    /**
     * Throughout operator used for a transaction that is going to commit 
     */
    public static final Modality TOUTTRC = new Modality(new Name("throughout_trc"));
    /**
     * Diamond operator used for a transaction that is going to abort
     */
    public static final Modality DIATRA = new Modality(new Name("diamond_tra"));
    /**
     * Box operator used for a transaction that is going to abort
     */
    public static final Modality BOXTRA = new Modality(new Name("box_tra"));
    /**
     * Throughout operator used for a transaction that is going to abort
     */
    public static final Modality TOUTTRA = new Modality(new Name("throughout_tra"));
    /**
     * Diamond operator used for a transaction that is suspended
     */
    public static final Modality DIASUSP = new Modality(new Name("diamond_susp"));
    /**
     * Box operator used for a transaction that is suspended
     */
    public static final Modality BOXSUSP = new Modality(new Name("box_susp"));
    /**
     * Throughout operator used for a transaction that is suspended
     */
    public static final Modality TOUTSUSP = new Modality(new Name("throughout_susp"));
    /** the wary substitution operator {var<-term}'. {x<-d}'A(x) means
     * replace all free occurrences of variable x in A with d, however
     * without replacing x with a non-rigid A below modalities */
    public static final SubstOp SUBST = new WarySubstOp(new Name("subst"));

    /** the true constant */
    public static final Junctor TRUE = new Junctor(new Name("true"),0);
    /** the false constant */
    public static final Junctor FALSE = new Junctor(new Name("false"),0);
    /** the null pointer */
    public static final Function NULL = new RigidFunction(new Name("null"),
						     Sort.NULL, 
						     new Sort[0]);

    /** the 'if-then-else' operator */
    public static final IfThenElse IF_THEN_ELSE = new IfThenElse ();

    /** the 'ifEx-then-else' operator */
    public static final IfExThenElse IF_EX_THEN_ELSE = new IfExThenElse ();

    /** control operator required for specification computation */
    public static final Junctor COMPUTE_SPEC_OP = new ComputeSpecOp();
   
    protected final Name name;
   	
    protected Op(Name name) {
	this.name=name;
    }
    
    protected boolean equalsForResolve(Operator op) {
	if (op.name().equals(this.name())) {
	    if (op.getClass() == this.getClass()) {
		if (op instanceof Junctor) {
		    if (((Junctor)op).arity() == ((Junctor)this).arity()) {
			return true;
		    } 
		} else {
		    return true;
		}
	    } 
	}
	return false;
    }

    
    protected Object readResolve() 
	throws ObjectStreamException {	

	Op[] op = {Op.NOT, Op.AND, Op.OR, Op.IMP,
		   Op.ALL, Op.EX,
		   Op.DIA, Op.BOX, Op.TOUT,
		   Op.DIATRC, Op.BOXTRC, Op.TOUTTRC,
		   Op.DIATRA, Op.BOXTRA, Op.TOUTTRA,
		   Op.DIASUSP, Op.BOXSUSP, Op.TOUTSUSP,
                   Op.SUBST, Op.TRUE,
		   Op.FALSE};
	for (int i=0;i<op.length;i++) {
	    if (equalsForResolve(op[i])) {
		return op[i];
	    }
	}
	return this;
    }
    
    /**
     * Returns a modality corresponding to a string
     * @param str name of the modality to return
     */
    public static Modality getModality(String str) {
	return (Modality)Modality.getNameMap().get(str);
    }

    public Name name() {
	return name;
    }
	
    public String toString() {
	return name().toString();
    }

    /**
     * @return true if the value of "term" having this operator as
     * top-level operator and may not be changed by modalities
     */
    public boolean isRigid (Term term) {
	return term.hasRigidSubterms ();
    }
        
    /** 
     * implements the default operator matching rule which means 
     * that the compared object have to be equal otherwise
     * matching fails
     */
    public MatchConditions match(SVSubstitute subst, MatchConditions mc,
            Services services) {
        if (subst == this) {
            return mc;
        }
        Debug.out("FAILED. Operators are different(template, candidate)", this, subst);
        return null;
    }
}
