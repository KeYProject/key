// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.logic;

import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.util.Debug;

/** 
 * In contrast to the distinction of formulas and terms as made by most of the 
 * inductive definition of the syntax of a logic, an instance of this class can
 * stand for a term or a formula. This is done for implementation reasons, as
 * their structure is quite similar and there are good reasons concerning the
 * software's design/architecture (for example using same visitors, reduction of
 * case distinction, unified interfaces etc.). However, they are strictly
 * separated by their sorts. A formula (and just a formula) must have 
 * the sort {@link Sort#FORMULA}. Terms of a different sort are terms in the
 * customary logic sense. A term of sort formula is allowed exact there, where a
 * formuala in logic is allowed to appear, same for terms of different sorts. 
 *   Some words about other design decisions: 
 * <ol> 
 *  <li> terms are immutable, this means after a term object is created, it
 *  cannot be changed. The advantage is that we can use term sharing and
 *  saving a lot of memory space. 
 *  </li>
 *  <li> Term has to be created using the {@link TermFactory} and
 *    <emph>not</emph> by using the constructors itself. 
 *  </li>
 *  <li> Term is subclassed, but all subclasses have to be package private, so
 *    that all other classes except {@link TermFactory} know only the class
 *    Term and its interface. Even most classes of the logic package.
 *  </li>
 *  <li> as it is immutable, most (all) attributes should be declared final
 * </li>
 * </ol>
 * Term supports the {@link Visitor} pattern. Two different visit strategies are
 * currently supported: {@link Term#execPostOrder(Visitor)} and
 * {@link Term#execPreOrder(Visitor)}. 
 */
public abstract class Term implements SVSubstitute {

    /** empty list of variables */
    public static final ArrayOfQuantifiableVariable EMPTY_VAR_LIST = 
	new ArrayOfQuantifiableVariable(new QuantifiableVariable[0]);

   /** the top level operator of this term */
    private final Operator op;

    /** caches the sort of this term */
    private final Sort sort;
    
    /** caches the hashcode of the term */
    private int hashcode;
    
    /** true iff this term is rigid */
    private boolean rigid;
    private boolean rigidComputed = false; 

    /** 
     * caches the free variables of this term  
     */
    private SetOfQuantifiableVariable freeVars = null; 

    /** caches the meta variables of this term */
    private SetOfMetavariable metaVars = null;

    /** 
     * creates a Term with top operator op
     * @param op Operator at the top of the termstructure that starts
     * here.
     * @param sort the Sort of the term
     */
    protected Term(Operator op, Sort sort) {
	this.op       = op;
	this.sort     = sort;
    }

    
    /**
     * returns the arity of the term  
     * @return arity of the term 
     * */
    public abstract int arity();

    protected int calculateHash(){
	int hashValue = 5;
	hashValue = hashValue*17 + op().hashCode();  
	hashValue = hashValue*17 + sort().hashCode();
	
        for(int i = 0, ar = arity() ; i<ar; i++){
	   hashValue = hashValue*17 + varsBoundHere(i).size();
	   hashValue = hashValue*17 + sub(i).hashCode();
	}
	hashValue = hashValue*17 + javaBlock().hashCode();
        if (hashValue == 0) return 1;
	
        return hashValue;
    }

    /**
     * checks whether the Term is valid on the top level. If this is
     * the case this method returns the Term unmodified. Otherwise a
     * TermCreationException is thrown.  
     * @return this Term if the top level of the Term is valid.
     */
    public Term checked() {
	if (op().validTopLevel(this)) {
	    return this;	    
	} else {	   	    
	    throw new TermCreationException(op(), this);
	}
    }

    /** 
     * returns the longest path from the top of the term to one of its leaves
     * @return an int representing the depth of this term
     */
    public abstract int depth();

    /**
     * this method has to be called by subclasses after they determined the
     * arity of the term. The method then can determine the free vars of the
     * term and put them in a cache.
     */
    private void determineFreeVarsAndMetaVars() {
	freeVars = SetAsListOfQuantifiableVariable.EMPTY_SET;
        metaVars = SetAsListOfMetavariable.EMPTY_SET;
        if (op instanceof QuantifiableVariable) {
            freeVars = freeVars.add((QuantifiableVariable) op);
        } else if ( op instanceof Metavariable ) {
            metaVars = metaVars.add ( (Metavariable)op );
        }
        for (int i = 0, ar = arity(); i<ar; i++) {
	    if (sub(i) == null) {
                Debug.fail("FREE "+op+" "+i);
	    }	        
	    SetOfQuantifiableVariable subFreeVars = sub(i).freeVars();
	    for (int j=0, sz = varsBoundHere(i).size(); j<sz; j++) {
		subFreeVars = subFreeVars.
		    remove(varsBoundHere(i)
			   .getQuantifiableVariable(j));
	    }
	    freeVars = freeVars.union(subFreeVars);
	    metaVars = metaVars.union(sub(i).metaVars());
	}
    }


    /**
     * this method has to be called by subclasses after they have
     * assigned the subterms of the term. The method then can
     * determine whether the operator and the subterms are rigid and
     * put this information in a cache.
     *
     * the implementation of this method uses the fact that
     * quantifiable variables are rigid; otherwise, the results are
     * too pessimistic (but still valid)
     */
    private void determineRigidness () {
	this.rigid = op ().isRigid ( this ) ;
	this.rigidComputed = true;
    }

    /**
     * true if <code>o</code> is syntactical equal to this term
     * @param o the Object to be compared with this term
     * @return true iff the given Term has the same values in
     * operator, sort, arity, varsBoundHere and javaBlock as this object.
     */
    public boolean equals(Object o) {
	if (o == this) return true;
	if (!(o instanceof Term)) return false;	

	final Term t = (Term) o;	

	if (!(sort() == t.sort() &&
	      arity() == t.arity() && 
	      op().equals(t.op()))) {
	    return false;
	}

	for (int i = 0, ar = arity(); i < ar; i++) {
	    if (varsBoundHere(i).size() != t.varsBoundHere(i).size()){
		return false;
	    }
	    for (int j = 0, sz = varsBoundHere(i).size(); j<sz; j++) {
		if (!varsBoundHere(i).getQuantifiableVariable(j).equals
		    (t.varsBoundHere(i).getQuantifiableVariable(j))) {
		    return false;
		}
	    }

	    if (!sub(i).equals(t.sub(i))) {
		return false;
	    }
	}
	return javaBlock().equals(t.javaBlock());
    }

    /**
     * compares if two terms are equal modulo bound renaming
     * @return true iff the given Term has the same values in
     * operator, sort, arity, varsBoundHere and javaBlock as this object
     * modulo bound renaming
     */  
    public boolean equalsModRenaming(Object o) {
        if (o == this) {
            return true;
        }       
        if (!(o instanceof Term)) {
	    return false;
	}
	final Constraint result = Constraint.BOTTOM.unify(this, (Term) o, null);

	return result == Constraint.BOTTOM;	
    }

    /** 
     * the visitor is handed through till the bottom of the tree and
     * then it walks upwards while at each upstep the method visit of
     * the visitor is called
     * @param visitor the Visitor
     */
    public void execPostOrder(Visitor visitor) {
	visitor.subtreeEntered(this);
	for (int i = 0, ar = arity(); i<ar; i++) {
	    sub(i).execPostOrder(visitor);
	}
	visitor.visit(this);
	visitor.subtreeLeft(this);
    }

    /** the visitor walks downwards the tree
     * while at each downstep the method visit of
     * the visitor is called
     * @param visitor the Visitor
     */
    public void execPreOrder(Visitor visitor) {
	visitor.subtreeEntered(this);
	visitor.visit(this);
	for (int i = 0, ar = arity(); i<ar; i++) {
	    sub(i).execPreOrder(visitor);
	}
	visitor.subtreeLeft(this);	
    }

    /** 
     * The primary diamond in this formula. Note that the default
     * implementation is the same as <code>javaBlock()</code> but
     * the semantics is different. See <code>SimultaneousUpdateTerm</code>.
     */
    public JavaBlock executableJavaBlock() {
        return javaBlock();
    }

    /** 
     * returns the set of free quantifiable variables occuring in this term
     * @return the SetOfFree 
     */
    public SetOfQuantifiableVariable freeVars() {
        if (freeVars == null) {
            determineFreeVarsAndMetaVars();
        }
        return freeVars;
    }

    /**
     * returns the hashcode of the term
     * @return the hashcode of the Term.
     */    
    public int hashCode(){
        if (hashcode == 0) {
            hashcode = calculateHash();
        }
        return hashcode;
    }

    /**
     * @return true iff all subterms of this term are rigid according
     * to the value the method "isRigid" returns for them (this does
     * not imply this term to be rigid itself!)
     */
    public boolean hasRigidSubterms () {
        for (int i = 0, ar = arity(); i<ar; i++) {
            if ( sub(i) == null ) {
                Debug.fail("FREE "+op+" "+i);
            }
            if ( !sub(i).isRigid () )
                return false;
        }

        return true;
    }

    /**
     * retrieves if the evaluation of the term is state independant. It is
     * guaranteed that if the result is <code>true</code> then the value is
     * state independant. In case of <code>false</code> no such guarantee is 
     * given i.e. the terms value may be the same in all states or not.
     * (safe approximation)  
     * @return false if the value of this term may be changed by
     * modalities (otherwise, however, the result may also be false)
     */
    public final boolean isRigid () {
        if (!rigidComputed ) {
            determineRigidness();
        }
            
       return rigid;
    }

    /** @return JavaBlock if term has diamond at the top level */
    public JavaBlock javaBlock() {
        return JavaBlock.EMPTY_JAVABLOCK;
    }

    /** 
     * returns the set of metavariables that are part of this term 
     * (metavariables are thought as placeholder for some gound term, whereas
     * the variables in <code>freeVars</code> are bound by some quantifier above)
     * @return the set of metavariables
     */
    public SetOfMetavariable metaVars () {
        if (metaVars == null) {
            determineFreeVarsAndMetaVars();
        }
        return metaVars;
    }

    /** 
     * the top operator in "A and B" it is "and", in f(x,y) it is "f"
     * @return operator at the top
     */
    public Operator op() {
        return op;
    }

    /**
     * returns the sort of the term
     * @return the sort of the term 
     */
    public Sort sort() {
        return sort;
    }

    /** 
     * returns the <code>nr</code>-th direct subterm 
     * @param nr the int specifying the <tt>nr</tt>-th direct subterm 
     */
    public abstract Term sub(int nr);

    /**
     * returns subterm at the position specified by the given PosInTerm pos.
     * @param pos the position of the wanted subterm
     * @return the subterm that is specified by pos
     */
    public Term subAt(PosInTerm pos) {
        Term sub = this;
        for (final IntIterator it = pos.iterator(); it.hasNext(); ) {	
            sub = sub.sub(it.next());
        }
        return sub;
    }

    /**
     * returns the array of variables the top level operator binds at the n-th
     * sub term 
     * @return the bound variables for the n-th subterm 
     */
    public abstract ArrayOfQuantifiableVariable varsBoundHere(int n);


    /**
     * returns a linearized textual representation of this term 
     */
    public String toString() {
        StringBuffer sb = new StringBuffer(op().name().toString());
        if (arity() == 0) return sb.toString();
        sb.append("(");
        for (int i = 0, ar = arity(); i<ar; i++) {
            for (int j=0, vbSize = varsBoundHere(i).size(); j<vbSize; j++) {
                if (j == 0) {
                    sb.append("{");
                }
                sb.append(varsBoundHere(i).getQuantifiableVariable(j));
                if (j!=varsBoundHere(i).size()-1) {
                    sb.append(", ");
                } else {
                    sb.append("}");
                }
            }
            sb.append(sub(i));
            if (i < ar-1) {
                sb.append(",");
            }
        }
        sb.append(")");
        return sb.toString();
    }	


//  =============== For debugging, used in Main (COMPUTE_SPEC_OP-Z) =================

    public void tree() {
        System.out.println("==============================");
        tree(this, 0);
    }


    private void tree(Term t, int off) {
        int i;
        for (i=0; i<off; i++) System.out.print(" ");
        String s = t.op().toString();
        s = s.substring(s.lastIndexOf(".")+1, s.length());
        System.out.println(t+" ["+s+"]");
        for (i=0; i<t.arity(); i++) tree(t.sub(i), off+3);
    }

}
