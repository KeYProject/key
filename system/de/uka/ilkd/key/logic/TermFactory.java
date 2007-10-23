// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//


package de.uka.ilkd.key.logic;

import java.util.*;

import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.*;
import de.uka.ilkd.key.rule.ListOfUpdatePair;
import de.uka.ilkd.key.rule.UpdatePair;
import de.uka.ilkd.key.util.Debug;
import de.uka.ilkd.key.util.LRUCache;

/** 
 * The TermFactory is the <em>only</em> way to create terms using constructos of
 * class Term or any of its subclasses. It is the
 * only class that implements and may exploit knowledge about sub
 * classes of {@link Term} all other classes of the system only know
 * about terms what the {@link Term} class offers them. 
 * 
 * This class is used to encapsulate knowledge about the internal term structures.
 * See {@link de.uka.ilkd.key.logic.TermBuilder} for more convienient methods to create
 * terms. 
 */
public class TermFactory {

    /**
     * class used a key for term cache if more than one composite needs 
     * to be compared
     * Attention: for complex terms comparing may be too expensive in these
     * cases do not cache them
     */
    static class CacheKey {
        
        private final static Object DUMMY_KEY_COMPOSITE = new Object();
        
        private final Object o1, o2, o3;
        
        /**
         * the first key composite is compared by identity
         * the second key composite is compared via equals
         * @param o1 the first key composite
         * @param o2 the second key composite (non null)
         */
        public CacheKey(Object o1, Object o2) {
            this.o1 = o1;
            this.o2 = o2;
            this.o3 = DUMMY_KEY_COMPOSITE;
        }
        
        /**
         * the first key composite is compared by identity
         * the second and third key composite is compared via equals
         * @param o1 the first key composite
         * @param o2 the second key composite (non null)
         * @param o3 the third key composite (non null)
         */
        public CacheKey(Object o1, Object o2, Object o3) {
            this.o1 = o1;
            this.o2 = o2;
            this.o3 = o3;
        }
        

        public int hashCode() {
            return o1.hashCode() + 17*o2.hashCode() + 7*o3.hashCode(); 
        }
        
        public boolean equals(Object o) {
            if (!(o instanceof CacheKey)) {
                return false;
            }
            final CacheKey ck = (CacheKey) o;
            return o1 == ck.o1 && o2.equals(ck.o2) && o3.equals(ck.o3);
        }
        
    }

    private static Map cache = Collections.synchronizedMap(new LRUCache(5000));

    
    /** An instance of TermFactory */
    public static final TermFactory DEFAULT=new TermFactory();

    private static final Term[] NO_SUBTERMS = new Term[0];

    /** creates t[index] with top operand op
     */
    public Term createArrayTerm(ArrayOp op, Term t, Term index){
	if (op==null) {
            throw new IllegalArgumentException("null-Operator at"+                    
							 "TermFactory");
        }      
        return new OpTerm(op, new Term[]{t, index}).checked();
    }


    /** 
     * creates a term representing a shadowed array access on the
     * <code>index</code>-th component of <code>t</code>
     * @param op the ShadowArrayOp used to access "shadowed memory
     * areas"
     * @param t the Term representing the array whose
     * <code>index</code> component is accessed
     * @param index the Term describing the index of the array
     * component to be accessed
     * @param shadownum the Term describing the nested scope of
     * shadowed access
     * @returns the term representing a shadowed array access on the
     * <code>index</code> component of <code>t</code> with a shadow
     * depth of <code>shadownum</code>
     */
    public Term createShadowArrayTerm(ShadowArrayOp op, Term t, Term index, Term shadownum){
	if (op==null) {
	    throw new IllegalArgumentException("Creation of a shadowed array access term" +
                        "failed due to missing operator."); 
	}
	return new OpTerm(op, new Term[]{t, index, shadownum}).checked();
    }

    /** 
     * creates a term representing a shadowed access on a multi
     * dimensional array. The exact component is specified by the
     * array of indices.
     * @param op the ShadowArrayOp used to access "shadowed memory
     * areas"
     * @param t the Term representing the array whose
     * <code>index</code> component is accessed
     * @param index an array of Term specifying the array component to
     * be accessed
     * @param shadownum the Term describing the nested scope of
     * shadowed access
     * @returns the term representing a shadowed array access on the
     * specified component of <code>t</code> with a shadow
     * depth of <code>shadownum</code>
     */
    public Term createShadowArrayTerm(ShadowArrayOp op, Term t, Term[] index, Term shadownum){
	if (op==null) {
	    throw new IllegalArgumentException("null-Operator at TermFactory"); 
	}
        final Term[] t1 = new Term[3];
        t1[0] = t;
        
        for(int i=0;i<index.length;i++){
	    t1[1] = index[i];
	    t1[2] = shadownum;
	    t1[0] = new OpTerm(op, t1).checked();
	}
	
        return t1[0];
    }
	
    /** 
     * creates a term representing an array access on the
     * <code>index</code>-th component of <code>t</code> 
     * @param op the ArrayOp used to access an array of type of
     * <code>t</code>
     * @param t the Term representing the array to be accessed
     * @param index the Term describing the index of the array
     * component to be accessed
     */
    public Term createArrayTerm(ArrayOp op, Term t, Term[] index){
	if (op == null) {
	    throw new IllegalArgumentException("null-Operator at TermFactory"); 
	}
        final Term[] t1 = new Term[2];
        t1[0]=t;
        for(int i=0;i<index.length;i++){
	    t1[1] = index[i];
	    t1[0] = new OpTerm(op, t1).checked();
	}
	return t1[0];
    }

    /**
     * @param arrayOp the shadowed or normal version of the array
     * access operator 
     * @param subs array of subterms
     * @return the term representing an array access
     */
    public Term createArrayTerm(ArrayOp arrayOp, Term[] subs) {
       if (arrayOp==null) {
           throw new IllegalArgumentException
               ("null-Operator at TermFactory");
       }       
       Term arrayTerm;
       if (subs.length == 2) {
           // we cache only the most common case
           final CacheKey key = new CacheKey(arrayOp, subs[0], subs[1]);
           arrayTerm = (Term) cache.get(key);
           if (arrayTerm == null) {
               arrayTerm = new OpTerm(arrayOp, subs).checked();
               cache.put(key, arrayTerm);
           }
           
       } else {
           arrayTerm = new OpTerm(arrayOp, subs).checked();
       }
 
       return arrayTerm;
    }

    
    public Term createAttributeTerm(AttributeOp op, Term term) {
	Debug.assertFalse(op instanceof ShadowedOperator, 
			  "Tried to create a shadowed attribute.");
	if (op.attribute() instanceof ProgramVariable && 
	    ((ProgramVariable)op.attribute()).isStatic()) {
	    return new OpTerm(op.attribute(), NO_SUBTERMS).checked();
	} 
	return new OpTerm(op, new Term[]{term}).checked();
    }
    
    /**
     * creates a term representing an attribute access
     * @param attrOp the AttributeOp representing the attribute to be accessed
     * @param subs an array of Term containing the subterms (usually of 
     * length 1 but may have length 2 for shadowed accesses) 
     * @return the term <code>subs[0].attr</code> 
     * (or <code>subs[0]^(subs[1]).attr)</code>)
     */
    public Term createAttributeTerm(AttributeOp attrOp, Term[] subs) {
        if (attrOp instanceof ShadowedOperator) {
            return createShadowAttributeTerm
                ((ShadowAttributeOp)attrOp, subs[0], subs[1]);
        }
        return createAttributeTerm(attrOp, subs[0]);
    }

    /** creates an attribute term that references to a field of a class
     * @param var the variable the attribute term references to
     * @param term the Term describing the class/object of which the
     * attribute value has to be determined
     * @return the attribute term "term.var"
     */
    public Term createAttributeTerm(ProgramVariable var, 
            Term term) {
	if (var.isStatic()) {
	    return createVariableTerm(var);
	}        
        
        final CacheKey key = new CacheKey(var, term);
        Term attrTerm = (Term) cache.get(key);
        if (attrTerm == null){
            attrTerm = new OpTerm(AttributeOp.getAttributeOp(var),
                    new Term[]{term}).checked();
            cache.put(key, attrTerm);
        } 
        return attrTerm;
    }
    
    /** 
     * creates an attribute term that references to a field of a class 
     * @param var the variable the attribute term references to
     * @param term the Term describing the class/object of which the
     * attribute value has to be determined      
     * @return the attribute term "term.var"
     */
    public Term createAttributeTerm(SchemaVariable var, Term term) {
	return new OpTerm
	    (AttributeOp.getAttributeOp((IProgramVariable)var), 
	     new Term[]{term}).checked();
    }


    public Term createBoxTerm(JavaBlock javaBlock, Term subTerm) {
	return createProgramTerm(Op.BOX, javaBlock, subTerm);
    }


    public Term createDiamondTerm(JavaBlock javaBlock, Term subTerm) {        
	return createProgramTerm(Op.DIA, javaBlock, subTerm);
    }


    /**
     * creates a EqualityTerm with a given equality operator. USE THIS WITH
     * CARE! THERE IS NO CHECK THAT THE EQUALITY OPERATOR MATCHES THE TERMS.
     */
    public Term createEqualityTerm(Equality op, Term[] subTerms) {	
        return new OpTerm(op, subTerms).checked();
    }

    /**
     * creates an EqualityTerm with a given equality operator. USE THIS WITH
     * CARE! THERE IS NO CHECK THAT THE EQUALITY OPERATOR MATCHES THE TERMS.
     */
    public Term createEqualityTerm(Equality op, Term t1, Term t2) {
	return createEqualityTerm(op, new Term[]{t1, t2});
    }
     
    /** create an EqualityTerm with the correct equality symbol for
     * the sorts involved, according to {@link Sort#getEqualitySymbol}
     */
    public Term createEqualityTerm(Term t1, Term t2) {
	return createEqualityTerm(new Term[]{t1, t2});

    }


    /** create an EqualityTerm with the correct equality symbol for
     * the sorts involved, according to {@link Sort#getEqualitySymbol}
     */
    public Term createEqualityTerm(Term[] terms) {
        Equality eq = terms[0].sort().getEqualitySymbol();
        if (terms[0].op() instanceof SchemaVariable) {
            eq = terms[1].sort().getEqualitySymbol();
        } 
        if (eq == null) eq = Op.EQUALS;
        
        return createEqualityTerm(eq, terms);
    }
    
    public Term createFunctionTerm(TermSymbol op) {
        Term result = (Term) cache.get(op);
        if (result == null) {
            result = createFunctionTerm(op, NO_SUBTERMS);
            cache.put(op, result);
        } 
        return result;
    }

    public Term createFunctionTerm(TermSymbol op, Term s1) {
        final CacheKey key = new CacheKey(op, s1);
        Term result = (Term) cache.get(key);
        if (result == null) {
            result = createFunctionTerm(op, new Term[]{s1});
            cache.put(key, result);
        } 
        return result;
    }

    public Term createFunctionTerm(TermSymbol op, Term s1, Term s2) {	
        final CacheKey key = new CacheKey(op, s1, s2);
        Term result = (Term) cache.get(key);
        if (result == null) {
            result = createFunctionTerm(op, new Term[]{s1,s2});
            cache.put(key, result);
        } 
        return result;
    }

     /** 
      * creates a term representing a function or predicate 
      * @param op a TermSymbol which is the top level operator of the
      * function term to be created
      * @param subTerms array of Term containing the sub terms,
      * usually the function's or predicate's arguments
      * @return a term with <code>op</code> as top level symbol and
      * the terms in <code>subTerms</code> as arguments (direct
      * subterms)
      */
    public Term createFunctionTerm(TermSymbol op, Term[] subTerms) {
	if (op==null) throw new IllegalArgumentException("null-Operator at"+
							 "TermFactory");
	
	return new OpTerm(op, subTerms).checked();
    }


    //For OCL simplification

    /** creates a term representing an OCL expression with a
      * collection operation as top operator that 
      * takes an OclExpression as argument (not "iterate")
      * @param op the OCL collection operation
      * @param varBoundHere the iterator variable
      * @param subs subs[0] is the collection and subs[1] is the 
      *        expression in which the iterator variable is bound
      */

    public Term createFunctionWithBoundVarsTerm(TermSymbol op,
						PairOfTermArrayAndBoundVarsArray subs) {
	return createFunctionWithBoundVarsTerm(op, subs.getTerms(), subs.getBoundVars());
    }

    public Term createFunctionWithBoundVarsTerm(TermSymbol op,
						Term[] subTerms,
						ArrayOfQuantifiableVariable[] boundVars) {
	if (boundVars != null) {
	   return new BoundVarsTerm(op, subTerms, boundVars).checked(); 
	} else {
	    return createFunctionTerm(op, subTerms);
	}
     }
    
    
    /**
     * Create an 'if-then-else' term (or formula)
     */
    public Term createIfThenElseTerm(Term condF, Term thenT, Term elseT) {
        return new OpTerm ( Op.IF_THEN_ELSE,
                            new Term [] { condF, thenT, elseT } );
    }
    

    /**
     * Create an 'ifEx-then-else' term (or formula)
     */
    public Term createIfExThenElseTerm(ArrayOfQuantifiableVariable exVars,
                                       Term condF, Term thenT, Term elseT) {
        return new IfExThenElseTerm ( Op.IF_EX_THEN_ELSE,
                                      new Term [] { condF, thenT, elseT },
                                      exVars ).checked();
    }
    


    /** some methods to handle the equality for formulas (equiv - operator) ... */
    public Term createJunctorTerm(Equality op, Term t1, Term t2) {
	return createEqualityTerm(op, new Term[]{t1, t2});
    }
    
    public Term createJunctorTerm(Equality op, Term[] subTerms) {
	return createEqualityTerm(op, subTerms);
    }

    public Term createJunctorTermAndSimplify(Equality op, Term t1, Term t2) {
        if ( op == Op.EQV ) {
            if ( t1.op () == Op.TRUE ) return t2;
            if ( t2.op () == Op.TRUE ) return t1;
            if ( t1.op () == Op.FALSE )
                return createJunctorTermAndSimplify ( Op.NOT, t2 );
            if ( t2.op () == Op.FALSE )
                return createJunctorTermAndSimplify ( Op.NOT, t1 );
            if ( t1.equals ( t2 ) ) return createJunctorTerm ( Op.TRUE );
        }
        return createEqualityTerm ( op, new Term [] { t1, t2 } );
    }

    public Term createJunctorTerm(Junctor op) {     
	return createJunctorTerm(op, NO_SUBTERMS);
    }

    public Term createJunctorTerm(Junctor op, Term t1) {
	return createJunctorTerm(op, new Term[]{t1});
    } 

    public Term createJunctorTerm(Junctor op, Term t1, Term t2) {
	return createJunctorTerm(op, new Term[]{t1, t2});
    }
 
    

    /** creates a JunctorTerm with top operator op, some subterms
     * @param op Operator at the top of the termstructure that starts
     * here
     * @param subTerms an array containing subTerms (an array with length 0 if
     * there are no more subterms */
    public Term createJunctorTerm(Junctor op, Term[] subTerms) {
	if (op==null) throw new IllegalArgumentException("null-Operator at"+
							 "TermFactory");
	return new OpTerm(op, subTerms).checked();
    }
    
    /** some methods for the creation of junctor terms with automatically performed simplification
     * like  ( b /\ true ) == (b) ...
     * Currently only the AND, OR, IMP Operators will be simplified (if possible)
     */
    public Term createJunctorTermAndSimplify(Junctor op, Term t1) {
        if (op == Op.NOT) {
            if (t1.op() == Op.TRUE) {
                return createJunctorTerm(Op.FALSE);
            } else if (t1.op() == Op.FALSE) {
                return createJunctorTerm(Op.TRUE);
            }
        }
        return createJunctorTerm(op, t1);
    }

    /** some methods for the creation of junctor terms with automatically performed simplification
     * like  ( b /\ true ) == (b) ...
     * Currently only the AND, OR, IMP Operators will be simplified (if possible)
     */
    public Term createJunctorTermAndSimplify(Junctor op, Term t1, Term t2) {
	if (op == Op.AND) {
	    // if one of the terms is false the expression is false as a whole
	    if (t1.op() == Op.FALSE || t2.op() == Op.FALSE)
	        return createJunctorTerm(Op.FALSE);
	    // if one of the terms is true skip the subterm.
	    if (t1.op() == Op.TRUE) {
		return  t2;
	    } else if(t2.op() == Op.TRUE) {
		return t1;
	    } else { // nothing to simplifiy ...
		return createJunctorTerm(op, t1, t2);
	    }
	} else if (op == Op.OR) {
	    // if one of the terms is true the expression is true as a whole
	    if (t1.op() == Op.TRUE || t2.op() == Op.TRUE)
		return createJunctorTerm(Op.TRUE);
	    // if one of the terms is false skip the subterm.
	    if (t1.op() == Op.FALSE) {
		return t2;
	    } else if(t2.op() == Op.FALSE) {
		return t1;
	    } else { // nothing to simplifiy ...
		return createJunctorTerm(op, t1, t2);
	    } 
	} else if (op == Op.IMP) {
	    if (t1.op() == Op.FALSE || t2.op() == Op.TRUE)
		// then the expression is true as a whole
		return createJunctorTerm(Op.TRUE);
	    // if t1 is true or t2 is false skip that subterm.
	    if (t1.op() == Op.TRUE) {
		return t2;
	    } else if(t2.op() == Op.FALSE) {
		return createJunctorTermAndSimplify(Op.NOT, t1);
	    } else { // nothing to simplifiy ...
		return createJunctorTerm(op, t1, t2);
	    }
        } else { // all other Junctors ...
	    return createJunctorTerm(op, t1, t2);
	}
    }

     /** creates a OpTerm with a meta operator as top operator. These
     * terms are only used in the replacewith areas of taclets. And are
     * replaced by the SyntacticalReplaceVisitor
     * @param op Operator at the top of the termstructure that starts
     * here
     * @param subTerms an array containing subTerms (an array with length 0 if
     * there are no more subterms
     */
    public Term createMetaTerm(MetaOperator op, Term[] subTerms) {
	if (op==null) throw new IllegalArgumentException("null-Operator at"+
							 "TermFactory");    
	return new OpTerm(op, subTerms).checked();
    }

    public Term createProgramTerm(Operator op, 
            JavaBlock javaBlock, 
            Term subTerm) {
	return new ProgramTerm(op, javaBlock, subTerm).checked();
    }


    public Term createProgramTerm(Operator op, 
            JavaBlock javaBlock, 
            Term[] subTerms) {
	return new ProgramTerm(op, javaBlock, subTerms).checked();
    }



    /**
     * creates a quantifier term 
     * @param quant the Quantifier (all, exist) which binds the
     * variables in <code>varsBoundHere</code> 
     * @param varsBoundHere an array of QuantifiableVariable
     * containing all variables bound by the quantifier
     * @param subTerm the Term where the variables are bound
     * @return the quantified term
     */
    public Term createQuantifierTerm(Quantifier quant,
				     ArrayOfQuantifiableVariable varsBoundHere, 
				     Term subTerm) {
	if (varsBoundHere.size()<=1) {
	    return new QuantifierTerm(quant, varsBoundHere, 
	            subTerm).checked();
	} else {
	    Term qt = subTerm;
	    for (int i=varsBoundHere.size()-1; i>=0; i--) {
		QuantifiableVariable qv 
		    = varsBoundHere.getQuantifiableVariable(i);
		qt = createQuantifierTerm(quant, qv, qt);
	    }
	    return qt;
	}	
    }



    /**
     * creates a quantifier term 
     * @param op Operator representing the
     * Quantifier (all, exist) of this term 
     * @param varsBoundHere a QuantifiableVariable representing the only bound
     * variable of this quantifier.
     */
    public Term createQuantifierTerm(Quantifier quant,
				     QuantifiableVariable var, 
				     Term subTerm) {
       return createQuantifierTerm
	   (quant, new QuantifiableVariable[]{var}, subTerm);
    }


    /**
     * creates a quantifier term 
     * @param op Operator representing the
     * Quantifier (all, exist) of this term 
     * @param varsBoundHere an
     * array of QuantifiableVariable containing all variables bound by the
     * quantifier
     */
    public Term createQuantifierTerm(Quantifier quant, 
				     QuantifiableVariable[] varsBoundHere, 
				     Term subTerm) {
	return createQuantifierTerm(quant, new ArrayOfQuantifiableVariable
	    (varsBoundHere), subTerm);
    }

    public Term createShadowAttributeTerm(ProgramVariable var, 
					    Term term, Term shadownum) {
	return new OpTerm(ShadowAttributeOp.getShadowAttributeOp(var), 
	        new Term[]{term, shadownum}).checked();
    }


    public Term createShadowAttributeTerm(SchemaVariable var,
					    Term term, Term shadownum) {
	return new OpTerm(ShadowAttributeOp.getShadowAttributeOp((IProgramVariable)var), 
	        new Term[]{term, shadownum}).checked();
    }
    
    public Term createShadowAttributeTerm(ShadowAttributeOp op, 
					    Term term, Term shadownum) {
	return new OpTerm(op, new Term[]{term, shadownum}).checked();
    }


     /** creates a substitution term
     * @param substVar the QuantifiableVariable to be substituted
     * @param substTerm the Term that replaces substVar
     * @param origTerm the Term that is substituted
     */
    public Term createSubstitutionTerm
	(SubstOp op, QuantifiableVariable substVar, 
	 Term substTerm, Term origTerm) {
	return new SubstitutionTerm
	    (op, substVar, new Term[]{substTerm, origTerm}).checked();
    }
    

     /** creates a substitution term
      * @param op the replacement variable
      * @param substVar the QuantifiableVariable to be substituted
      * @param subs an array of Term where subs[0] is the term that
      * replaces the variable substVar in subs[1] 
      */
    public Term createSubstitutionTerm(SubstOp op,
            QuantifiableVariable substVar, Term[] subs) {
	return new SubstitutionTerm(op, substVar, subs).checked();
    }


    /**
     * helper method for term creation (reduces duplicate code)
     */
    private Term createTermWithNoBoundVariables(Operator op, 
						Term[] subTerms, 
						JavaBlock javaBlock) {
	if (op instanceof Equality) {
	    return createEqualityTerm(subTerms);
	} else if (op instanceof TermSymbol) {
	    return createFunctionTerm((TermSymbol)op, subTerms);
	} else if (op instanceof Junctor) {
	    return createJunctorTerm((Junctor)op,subTerms);
	} else if (op instanceof AnonymousUpdate) {
            return createAnonymousUpdateTerm
	    ((AnonymousUpdate)op, subTerms[0]);
	} else if (op instanceof Modality) {
	    return createProgramTerm((Modality)op, javaBlock, subTerms[0]); 
	} else if (op instanceof AccessOp) {
	    if (op instanceof ShadowAttributeOp) {
		return createShadowAttributeTerm((ShadowAttributeOp)op, 
						 subTerms[0], subTerms[1]);
	    } else if (op instanceof AttributeOp) {
		return createAttributeTerm((AttributeOp)op, subTerms[0]);
	    } else if (op instanceof ArrayOp) {
		return createArrayTerm((ArrayOp)op, subTerms);
	    } else {
		Debug.fail("Unknown access operator" + op);
		return null;
	    }
	} else if (op instanceof IfThenElse) {
	    return createIfThenElseTerm ( subTerms[0], subTerms[1], subTerms[2] );
	} else if (op instanceof MetaOperator) {
	    return createMetaTerm((MetaOperator)op, subTerms);
	} else {
	    de.uka.ilkd.key.util.Debug.fail("Should never be"+
					    " reached. Missing case for class", 
					    op.getClass());
	    return null;
	}       	
    }

    public Term createTerm(Operator op, Term[] subTerms, 
			   ArrayOfQuantifiableVariable vars, 
			   JavaBlock javaBlock) {
	if (op==null) {
	    throw new IllegalArgumentException("null-Operator at TermFactory");
	} else if (op instanceof Quantifier) {
	    return createQuantifierTerm((Quantifier)op, vars, subTerms[0]);
	} else if ( op instanceof QuanUpdateOperator ) {
	    final ArrayOfQuantifiableVariable[] bv =
	        new ArrayOfQuantifiableVariable [subTerms.length];
            final QuanUpdateOperator updOp = (QuanUpdateOperator)op;
            Arrays.fill ( bv, new ArrayOfQuantifiableVariable () );
            bv[0] = vars;
            return createQuanUpdateTerm ( updOp, subTerms, bv );
	} else if (op instanceof IfExThenElse) {
	    return createIfExThenElseTerm ( vars,
                                            subTerms[0],
                                            subTerms[1],
                                            subTerms[2] );
	} else if (op instanceof SubstOp) {
	    return createSubstitutionTerm((SubstOp)op, 
					  vars.getQuantifiableVariable(0),
					  subTerms);
	} else {
	    return createTermWithNoBoundVariables(op, subTerms, javaBlock);
	}
    }


   public Term createTerm(Operator op, Term[] subTerms, 
			  ArrayOfQuantifiableVariable[] bv,
			  JavaBlock javaBlock) {
	if (op==null) {
	    throw new IllegalArgumentException("null-Operator at TermFactory");
	} else if (op instanceof Quantifier) {
	    return createQuantifierTerm((Quantifier)op, bv[0], subTerms[0]);
	} else if (op instanceof QuanUpdateOperator) {
	    final QuanUpdateOperator updOp = (QuanUpdateOperator)op;
	    if ( bv == null ) {
	        bv = new ArrayOfQuantifiableVariable [subTerms.length];
                java.util.Arrays.fill ( bv, new ArrayOfQuantifiableVariable () );
	    }
	    return createQuanUpdateTerm (updOp, subTerms, bv);
	} else if (op instanceof IfExThenElse) {
	    final Term[] resTerms = new Term [3];
            System.arraycopy ( subTerms, 0, resTerms, 0, 3 );
	    final ArrayOfQuantifiableVariable exVars =
	        BoundVariableTools.DEFAULT.unifyBoundVariables ( bv, resTerms,
	                                                         0, 2 );
	    return createIfExThenElseTerm ( exVars,
                                            resTerms[0],
                                            resTerms[1],
                                            resTerms[2] );
	} else if (op instanceof SubstOp) {	    
	    return createSubstitutionTerm((SubstOp)op, 
					  bv[1].getQuantifiableVariable(0),
					  subTerms);
	} else if (op instanceof TermSymbol) { 
	    // special treatment for OCL operators binding variables	    
	    return createFunctionWithBoundVarsTerm((TermSymbol)op, subTerms, bv);	 
	} else {
	    return createTermWithNoBoundVariables(op, subTerms, javaBlock);
	}       
   }
    //
    // CHANGE these two methods!  vars should be something like an 
    // array of arrays! 
    //


    /**
     * creates a term using the other methods of this class depending on the
     * given operator. If the kind of term is known before (without using
     * if-else cascades on the kind of operator) the other methods in this
     * factory should be preferred. Depending on the needed parameters for
     * the terms that should be created some of the parameters of this method
     * might be ignored.
     * @param op the top level operator for the new term.
     * @param subTerms the subterms for the new term. The first n elements
     * are taken if op is a Junctor or TermSymbol and n is the arity
     * of op. Only the first entry is taken if op is a Quantifier or
     * a Diamond. The first (representing the replacing term
     * for a variable) and the second (representing the term behind the
     * substitution operator) entries are taken if op is a SubstOp.
     * @param vars the variables that are bound to a subterm. Not considered
     * if op is a Junctor, TermSymbol or Diamond. If op is a
     * SubstOp only the first element is taken and the variable is bound to
     * the second subterm. In all other cases all variables are taken and
     * bound to the first subterm.
     * @param javaBlock representing a java code block. Only taken if op is a
     * Diamond.
     * @return the created Term
     */
    public Term createTerm(Operator op, Term[] subTerms, 
			   QuantifiableVariable[] vars, 
			   JavaBlock javaBlock) {
	return createTerm(op, subTerms, new ArrayOfQuantifiableVariable(vars),
			  javaBlock);
    }

    /**
     * creates an update term like
     *    <code>{pair0}..{pairN}target</code>     
     */
    public Term createUpdateTerm(ListOfUpdatePair pairs, Term target) {
	if (pairs.size()>1) {
	    return createUpdateTerm(pairs.head(), 
				    (createUpdateTerm(pairs.tail(), 
						      target)));
	} else {
	    return createUpdateTerm(pairs.head(), target);
	}
    }
     
    
    /**
     * creates the update term <code>{loc:=value}target</code>
     * @param loc the Term representing the location to be updated
     * @param value the Term representing the value the location is updated to
     * @param target the Term on which the update is applied
     * @return the update term described above
     */
    public Term createUpdateTerm(Term loc, Term value, Term target) {
        return createUpdateTerm(new Term[] {loc}, new Term[] {value}, target);
    }
    
   
    /** 
     * creates an update term 
     *   <code>{locs[0]:=values[0],...,locs[n]:=values[n]}target</code>
     * where <code>n</code> is the length of the location array. 
     * @param locs an array of Term describing the updates locations
     * @param values an array of Term describing the values to which 
     * the locations are updated
     * @param target the Term on which the update is applied to
     * @return the update term as described above
     */
    public Term createUpdateTerm(Term[] locs, 
                                 Term[] values,
                                 Term target) {
        final ArrayOfQuantifiableVariable[] boundVars =
            new ArrayOfQuantifiableVariable [locs.length];
        Arrays.fill ( boundVars, new ArrayOfQuantifiableVariable () );
        final Term[] guards = new Term [locs.length];
        Arrays.fill ( guards, createJunctorTerm ( Op.TRUE ) );
        
        return createQuanUpdateTerm ( boundVars, guards, locs, values, target );
    }

    public Term createUpdateTerm(UpdatePair pair, 
                                 Term target) {

	final IUpdateOperator op = pair.updateOperator();
        
        if ( op instanceof AnonymousUpdate ) {      
            return createAnonymousUpdateTerm ( (AnonymousUpdate)op, target);
        } 
        
        final Term[] subs = new Term[pair.arity() + 1];
	
	for (int i = 0; i<subs.length-1; i++) {
	    subs[i] = pair.sub(i);	    
	}

	subs[subs.length-1] = target;

	if ( op instanceof QuanUpdateOperator ) {
            final ArrayOfQuantifiableVariable[] boundVars =
                new ArrayOfQuantifiableVariable [pair.arity () + 1];
            for ( int i = 0; i < subs.length - 1; i++ )
                boundVars[i] = pair.varsBoundHere ( i );
            boundVars[subs.length - 1] = new ArrayOfQuantifiableVariable ();
            return createQuanUpdateTerm ( (QuanUpdateOperator)op,
                                          subs,
                                          boundVars );
        } else {
            Debug.fail ( "Unknown update operator: " + op );
            return null; // unreachable
        }
    }
        
    /**
     * creates a normalized simultaneous update term
     * 
     * @param op
     *            the UpdateOperator
     * @param subs
     *            the subterm of the simultaneous update term to be created
     * @return the normalized simultaneous update term
     */
    public Term createNormalizedQuanUpdateTerm
                        (QuanUpdateOperator op,
                         Term[] subs,
                         ArrayOfQuantifiableVariable[] boundVarsPerSub) {
        return op.normalize ( boundVarsPerSub, subs );
    }

    /**
     * creates a simultaneous update-term
     * 
     * @param subs
     *            the sub-terms
     */
    public Term createQuanUpdateTerm
                        (QuanUpdateOperator op,
                         Term[] subs,
                         ArrayOfQuantifiableVariable[] boundVarsPerSub) {
        final ArrayOfQuantifiableVariable[] boundVars =
            op.toBoundVarsPerAssignment ( boundVarsPerSub, subs );
        return new QuanUpdateTerm ( op, subs, boundVars ).checked ();
    }

    /**
     * creates an update term which is not in normalform order (usually usage of
     * this method is discouraged)
     * 
     * @return creates an update term which is not in normalform order
     */
    public Term createQuanUpdateTermUnordered
        (QuanUpdateOperator op,
         Term[] subs,
         ArrayOfQuantifiableVariable[] boundVars) {
        
        return new QuanUpdateTerm ( op, subs, boundVars ).checked ();
    }

    /**
     * creates a normalized update term
     * <code>{locs[0]:=values[0],...,locs[n]:=values[n]}target</code> where
     * <code>n</code> is the length of the location array.
     * 
     * @param locs
     *            an array of Term describing the updates locations
     * @param values
     *            an array of Term describing the values to which the locations
     *            are updated
     * @param target
     *            the Term on which the update is applied to
     * @return the update term as described above
     */
    public Term createQuanUpdateTerm (ArrayOfQuantifiableVariable[] boundVars,
				      Term[] guards,
				      Term[] locs,
				      Term[] values,
				      Term target) {
        
        return QuanUpdateOperator
            .normalize ( boundVars, guards, locs, values, target );
    }


    /** 
     * creates a term consisting of the given variable.
     * @param v the variable
     */
    public Term createVariableTerm(LogicVariable v) {
        Term varTerm = (Term)cache.get(v);
        if (varTerm == null) {
            varTerm = new OpTerm(v, NO_SUBTERMS).checked();
            cache.put(v, varTerm);
        }
        return varTerm;
    }

    /**
     * creates a variable term representing the given programvariable
     * @param v the ProgramVariable to be represented
     * @return variable <code>v</code> as term 
     */
    public Term createVariableTerm(ProgramVariable v) {
        Term varTerm = (Term)cache.get(v);
        if (varTerm == null) {
            varTerm = new OpTerm(v, NO_SUBTERMS).checked();
            cache.put(v, varTerm);
        }
        return varTerm;
    }

    /**
     * creates a term with schemavariable <code>v</code> as top level operator     
     * @param v the SchemaVariable to be represented
     * @return the term <code>v</code>
     */
    public Term createVariableTerm(SchemaVariable v) {
        Term varTerm = (Term)cache.get(v);
        if (varTerm == null) {
            varTerm = new OpTerm(v, NO_SUBTERMS).checked();
            cache.put(v, varTerm);
        } 
        return varTerm;
    }


    /**
     * creates an anonymous update applied to the given target term 
     * @param op the AnonymousUpdate operator 
     * @param subs the array of Term containing the 
     * @return
     */
    public Term createAnonymousUpdateTerm(AnonymousUpdate op, 
            Term sub) {       
        return new UpdateTerm(op, new Term[]{sub});
    }

    /**
     * creates an anonymous update applied to the given target term 
     * @param name 
     * @param target
     * @return
     */
    public Term createAnonymousUpdateTerm(Name name, Term target) {       
        return createAnonymousUpdateTerm
        	(AnonymousUpdate.getAnonymousOperator(name),
        	     target);
    }

    /** creates a cast of term with to the given sort */    
    public Term createCastTerm(AbstractSort sort, Term with) {        
        return createFunctionTerm(sort.getCastSymbol(), with);
    }
    
}
