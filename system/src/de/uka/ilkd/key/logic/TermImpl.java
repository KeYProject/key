// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.logic;

import de.uka.ilkd.key.collection.*;
import de.uka.ilkd.key.java.NameAbstractionTable;
import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;


/**
 * The currently only class implementing the Term interface. TermFactory should
 * be the only class dealing directly with the TermImpl class.
 */
class TermImpl implements Term {

    private static final ImmutableArray<Term> EMPTY_TERM_LIST 
    	= new ImmutableArray<Term>();
    
    private static final ImmutableArray<QuantifiableVariable> EMPTY_VAR_LIST
    	= new ImmutableArray<QuantifiableVariable>();
	
    private static final ImmutableArray<TermLabel> EMPTY_LABEL_LIST
        = new ImmutableArray<TermLabel>();
    
    private static int serialNumberCounter =0;

    //content
    private final Operator op;
    private final ImmutableArray<Term> subs;
    private final ImmutableArray<QuantifiableVariable> boundVars;
    private final JavaBlock javaBlock;

    private int serialNumber = serialNumberCounter++;
    //caches
    private static enum ThreeValuedTruth { TRUE, FALSE, UNKNOWN }
    private int depth = -1;
    private ThreeValuedTruth rigid = ThreeValuedTruth.UNKNOWN; 
    private ImmutableSet<QuantifiableVariable> freeVars = null;
    private int hashcode = -1;
    
    /**
     * This flag indicates that the {@link Term} itself or one
     * of its children contains a non empty {@link JavaBlock}. 
     * {@link Term}s which provides a {@link JavaBlock} directly or indirectly
     * can't be cached because it is possible that the contained meta information
     * inside the {@link JavaBlock}, e.g. {@link PositionInfo}s, are different.
     */
    private boolean containsJavaBlockRecursive = false;
    
    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------
    
    public TermImpl(Operator op, 
	    	    ImmutableArray<Term> subs, 
	    	    ImmutableArray<QuantifiableVariable> boundVars, 
	    	    JavaBlock javaBlock) {
	assert op != null;
	assert subs != null;
	this.op = op;
	this.subs = subs.size() == 0 ? EMPTY_TERM_LIST : subs;
	this.boundVars = boundVars == null ? EMPTY_VAR_LIST : boundVars;	
	this.javaBlock = javaBlock == null 
	                 ? JavaBlock.EMPTY_JAVABLOCK 
	                 : javaBlock;
	computeContainsJavaBlockRecursive();
    }
    

        
    //-------------------------------------------------------------------------
    //internal methods
    //------------------------------------------------------------------------- 
    
    /**
     * Computes if a non empty {@link JavaBlock} is available in this {@link Term}
     * or in one of its direct or indirect children. The result is stored in
     * {@link #containsJavaBlockRecursive} available via {@link #isContainsJavaBlockRecursive()}.
     */
    private void computeContainsJavaBlockRecursive() {
        if (javaBlock != null && !javaBlock.isEmpty()) {
           containsJavaBlockRecursive = true;
        }
        else {
	  for (int i = 0; i<subs.size(); i++) {
              if (subs.get(i).isContainsJavaBlockRecursive()) {
                 containsJavaBlockRecursive = true;
		 return;
              }
           }
        }
    }

   private void determineFreeVars() {
	freeVars = DefaultImmutableSet.<QuantifiableVariable>nil();
        
        if(op instanceof QuantifiableVariable) {
            freeVars = freeVars.add((QuantifiableVariable) op);
        } 
        for(int i = 0, ar = arity(); i < ar; i++) {
	    ImmutableSet<QuantifiableVariable> subFreeVars = sub(i).freeVars();
	    for(int j = 0, sz = varsBoundHere(i).size(); j < sz; j++) {
		subFreeVars = subFreeVars.remove(varsBoundHere(i).get(j));
	    }
	    freeVars = freeVars.union(subFreeVars);	   
	}
    }
    
    
    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------
    
    /**
     * Checks whether the Term is valid on the top level. If this is
     * the case this method returns the Term unmodified. Otherwise a
     * TermCreationException is thrown.  
     */
    public Term checked() {
    	if(op().validTopLevel(this)) {
	    return this;	    
	} else {	   	    
	    throw new TermCreationException(op(), this);
	}
    }    
    
    @Override
    public Operator op() {
        return op;
    }
    
    
    @Override
    public ImmutableArray<Term> subs() {
	return subs;
    }
    
    
    @Override
    public Term sub(int nr) {
	return subs.get(nr);
    }
    
    
    @Override
    public Term subAt(PosInTerm pos) {
        Term sub = this;
        for(int i = 0; i<pos.depth(); i++) {	
            sub = sub.sub(pos.getIndexAt(i));
        }
        return sub;
    }
    
    
    @Override
    public ImmutableArray<QuantifiableVariable> boundVars() {
	return boundVars;
    }
    
        
    @Override
    public ImmutableArray<QuantifiableVariable> varsBoundHere(int n) {
	return op.bindVarsAt(n) ? boundVars : EMPTY_VAR_LIST;
    }
    
    
    @Override
    public JavaBlock javaBlock() {
	return javaBlock;
    }    
    
    
    @Override
    public int arity() {
	return op.arity();
    }
    
    
    @Override
    public Sort sort() {
	return op.sort(subs);
    }
    

    @Override
    public int depth() {
	if(depth == -1) {
            for (int i = 0, n = arity(); i < n; i++) {
                final int subTermDepth = sub(i).depth();
                if(subTermDepth > depth) {
                    depth = subTermDepth;   
                }
            }
            depth++;
	}
        return depth;
    }
    
    
    @Override
    public boolean isRigid() {
	if(rigid == ThreeValuedTruth.UNKNOWN) {
            if(!op.isRigid()) {
        	rigid = ThreeValuedTruth.FALSE;
            } else {
        	rigid = ThreeValuedTruth.TRUE;
        	for(int i = 0, n = arity(); i < n; i++) {
            	    if(!sub(i).isRigid()) {
            		rigid = ThreeValuedTruth.FALSE;
            		break;
            	    }
        	}
            }
        }
            
       return rigid == ThreeValuedTruth.TRUE;
    }
    

    @Override
    public ImmutableSet<QuantifiableVariable> freeVars() {
        if(freeVars == null) {
            determineFreeVars();
        }
        return freeVars;
    }
    
    @Override
    public void execPostOrder(Visitor visitor) {
	visitor.subtreeEntered(this);
	for(int i = 0, ar = arity(); i < ar; i++) {
	    sub(i).execPostOrder(visitor);
	}
	visitor.visit(this);
	visitor.subtreeLeft(this);
    }


    @Override
    public void execPreOrder(Visitor visitor) {
	visitor.subtreeEntered(this);
	visitor.visit(this);
	for (int i = 0, ar = arity(); i < ar; i++) {
	    sub(i).execPreOrder(visitor);
	}
	visitor.subtreeLeft(this);	
    }
    

    @Override
    public boolean equalsModRenaming(Object o) {
        if(o == this) {
            return true;
        }       
        if (!(o instanceof Term)) {
	    return false;
	}
	return unifyHelp ( this, ((Term) o),
           ImmutableSLList.<QuantifiableVariable>nil(), 
           ImmutableSLList.<QuantifiableVariable>nil(),
           null);
    }
    
    // 
    // equals modulo renaming logic
    
    
    /**
     * compare two quantifiable variables if they are equal modulo renaming
     * 
     * @param ownVar
     *            first QuantifiableVariable to be compared
     * @param cmpVar
     *            second QuantifiableVariable to be compared
     * @param ownBoundVars
     *            variables bound above the current position
     * @param cmpBoundVars
     *            variables bound above the current position
     */
    private static boolean compareBoundVariables(QuantifiableVariable ownVar,
	    QuantifiableVariable cmpVar,
	    ImmutableList<QuantifiableVariable> ownBoundVars,
	    ImmutableList<QuantifiableVariable> cmpBoundVars) {

	final int ownNum = indexOf(ownVar, ownBoundVars);
	final int cmpNum = indexOf(cmpVar, cmpBoundVars);

	if (ownNum == -1 && cmpNum == -1)
	    // if both variables are not bound the variables have to be the
	    // same object
	    return ownVar == cmpVar;

	// otherwise the variables have to be bound at the same point (and both
	// be bound)
	return ownNum == cmpNum;
    }

    /**
     * @return the index of the first occurrence of <code>var</code> in
     *         <code>list</code>, or <code>-1</code> if the variable is not an
     *         element of the list
     */
    private static int indexOf(QuantifiableVariable var,
	    ImmutableList<QuantifiableVariable> list) {
	int res = 0;
	while (!list.isEmpty()) {
	    if (list.head() == var)
		return res;
	    ++res;
	    list = list.tail();
	}
	return -1;
    }

    /**
     * Compares two terms modulo bound renaming
     * 
     * @param t0
     *            the first term
     * @param t1
     *            the second term
     * @param ownBoundVars
     *            variables bound above the current position
     * @param cmpBoundVars
     *            variables bound above the current position
     * @return <code>true</code> is returned iff the terms are equal modulo
     *         bound renaming
     */
    private boolean unifyHelp(Term t0, Term t1,
	    ImmutableList<QuantifiableVariable> ownBoundVars,
	    ImmutableList<QuantifiableVariable> cmpBoundVars,
	    NameAbstractionTable nat) {

	if (t0 == t1 && ownBoundVars.equals(cmpBoundVars))
	    return true;

	final Operator op0 = t0.op();

	if (op0 instanceof QuantifiableVariable)
	    return handleQuantifiableVariable(t0, t1, ownBoundVars,
		    cmpBoundVars);

	final Operator op1 = t1.op();

	if (!(op0 instanceof ProgramVariable) && op0 != op1)
	    return false;

	if (t0.sort() != t1.sort() || t0.arity() != t1.arity())
	    return false;

	nat = handleJava(t0, t1, nat);
	if (nat == FAILED)
	    return false;

	return descendRecursively(t0, t1, ownBoundVars, cmpBoundVars, nat);
    }

    private boolean handleQuantifiableVariable(Term t0, Term t1,
	    ImmutableList<QuantifiableVariable> ownBoundVars,
	    ImmutableList<QuantifiableVariable> cmpBoundVars) {
	if (!((t1.op() instanceof QuantifiableVariable) && compareBoundVariables(
	        (QuantifiableVariable) t0.op(), (QuantifiableVariable) t1.op(),
	        ownBoundVars, cmpBoundVars)))
	    return false;
	return true;
    }

    /**
     * used to encode that <tt>handleJava</tt> results in an unsatisfiable
     * constraint (faster than using exceptions)
     */
    private static NameAbstractionTable FAILED = new NameAbstractionTable();

    private static NameAbstractionTable handleJava(Term t0, Term t1,
	    NameAbstractionTable nat) {

	if (!t0.javaBlock().isEmpty() || !t1.javaBlock().isEmpty()) {
	    nat = checkNat(nat);
	    if (!t0.javaBlock().equalsModRenaming(t1.javaBlock(), nat)) {
		return FAILED;
	    }
	}

	if (!(t0.op() instanceof SchemaVariable)
	        && t0.op() instanceof ProgramVariable) {
	    if (!(t1.op() instanceof ProgramVariable)) {
		return FAILED;
	    }
	    nat = checkNat(nat);
	    if (!((ProgramVariable) t0.op()).equalsModRenaming(
		    (ProgramVariable) t1.op(), nat)) {
		return FAILED;
	    }
	}

	return nat;
    }

    private boolean descendRecursively(Term t0, Term t1,
	    ImmutableList<QuantifiableVariable> ownBoundVars,
	    ImmutableList<QuantifiableVariable> cmpBoundVars,
	    NameAbstractionTable nat) {

	for (int i = 0; i < t0.arity(); i++) {
	    ImmutableList<QuantifiableVariable> subOwnBoundVars = ownBoundVars;
	    ImmutableList<QuantifiableVariable> subCmpBoundVars = cmpBoundVars;

	    if (t0.varsBoundHere(i).size() != t1.varsBoundHere(i).size())
		return false;
	    for (int j = 0; j < t0.varsBoundHere(i).size(); j++) {
		final QuantifiableVariable ownVar = t0.varsBoundHere(i).get(j);
		final QuantifiableVariable cmpVar = t1.varsBoundHere(i).get(j);
		if (ownVar.sort() != cmpVar.sort())
		    return false;

		subOwnBoundVars = subOwnBoundVars.prepend(ownVar);
		subCmpBoundVars = subCmpBoundVars.prepend(cmpVar);
	    }

	    boolean newConstraint = unifyHelp(t0.sub(i), t1.sub(i),
		    subOwnBoundVars, subCmpBoundVars, nat);

	    if (!newConstraint)
		return false;
	}

	return true;
    }

    private static NameAbstractionTable checkNat(NameAbstractionTable nat) {
	if (nat == null)
	    return new NameAbstractionTable();
	return nat;
    }
    
    // end of equals modulo renaming logic
    

    /**
     * true iff <code>o</code> is syntactically equal to this term
     */
    @Override
    public boolean equals(Object o) {
	if(o == this) {
	    return true;
	}
	
	if(!(o instanceof Term)
	    || hashCode() != o.hashCode()) {
	    return false;	
	}
	final Term t = (Term) o;
	
	return op().equals(t.op())
	       && t.hasLabels() == hasLabels()
		   && subs().equals(t.subs())
	       && boundVars().equals(t.boundVars())
	       && javaBlock().equals(t.javaBlock());
    }


    @Override
    public int hashCode(){
        if(hashcode == -1) {
            hashcode = 5;
            hashcode = hashcode*17 + op().hashCode();
            hashcode = hashcode*17 + subs().hashCode();
            hashcode = hashcode*17 + boundVars().hashCode();            
            hashcode = hashcode*17 + javaBlock().hashCode();
            
            if(hashcode == -1) {
        	hashcode = 0;
            }
        }
        return hashcode;
    }


    /**
     * returns a linearized textual representation of this term 
     */
    @Override    
    public String toString() {
	StringBuffer sb = new StringBuffer();
	if(!javaBlock.isEmpty()) {
	    if(op() == Modality.DIA) {
		sb.append("\\<").append(javaBlock).append("\\> ");
	    } else if (op() == Modality.BOX) {
		sb.append("\\[").append(javaBlock).append("\\] ");
	    } else {
		sb.append(op()).append("\\[").append(javaBlock).append("\\] ");
	    }
	    sb.append("(").append(sub(0)).append(")");
	    return sb.toString();
	} else {
            sb.append(op().name().toString());
            if(!boundVars.isEmpty()) {
       	    	sb.append("{");
       	    	for(int i = 0, n = boundVars.size(); i < n; i++) {
       	    	    sb.append(boundVars.get(i));
       	    	    if(i < n - 1) {
       	    		sb.append(", ");
       	    	    }     	       	    	    
       	    	}
       	    	sb.append("}");
            }
            if(arity() == 0) {
        	return sb.toString();
            }
            sb.append("(");
            for(int i = 0, ar = arity(); i < ar; i++) {
                sb.append(sub(i));
                if(i < ar - 1) {
                    sb.append(",");
                }
            }
            sb.append(")");
	}
	
        return sb.toString();
    }
   

    @Override
    public int serialNumber() {
        return serialNumber;
    }

    @Override
    public boolean hasLabels() {
        return false;
    }

    @Override
    public boolean containsLabel(TermLabel label) {
        return false;
    }

    @Override
    public ImmutableArray<TermLabel> getLabels() {
        return EMPTY_LABEL_LIST;
    }
    
    /**
     * {@inheritDoc}
     */
    @Override
    public boolean isContainsJavaBlockRecursive() {
        return containsJavaBlockRecursive;
    }
}