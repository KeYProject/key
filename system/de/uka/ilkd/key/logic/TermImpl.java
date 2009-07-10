// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
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


public final class TermImpl implements Term {

    private static final ArrayOfTerm EMPTY_TERM_LIST 
    	= new ArrayOfTerm();
    private static final ArrayOfQuantifiableVariable EMPTY_VAR_LIST
    	= new ArrayOfQuantifiableVariable();

    //content
    private final Operator op;
    private final ArrayOfTerm subs;
    private final JavaBlock javaBlock;
    private final ArrayOfQuantifiableVariable[] boundVars;
    
    //caches
    private static enum ThreeValuedTruth { TRUE, FALSE, UNKNOWN }
    private int depth = -1;
    private ThreeValuedTruth rigid = ThreeValuedTruth.UNKNOWN; 
    private SetOfQuantifiableVariable freeVars = null; 
    private SetOfMetavariable metaVars = null;
    private int hashcode = -1;
    
    
    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------
    
    public TermImpl(Operator op, 
	    	    ArrayOfTerm subs, 
	    	    JavaBlock javaBlock, 
	    	    ArrayOfQuantifiableVariable[] boundVars) {
	assert op != null;
	assert subs != null;
	assert javaBlock != null;
	this.op   = op;
	this.subs = subs.size() == 0 ? EMPTY_TERM_LIST : subs;
	this.javaBlock = javaBlock;
	if(boundVars != null) {
	    this.boundVars = new ArrayOfQuantifiableVariable[boundVars.length];
	    for(int i = 0; i < boundVars.length; i++) {
		this.boundVars[i] = boundVars[i];
	    }
	} else {
	    this.boundVars = null;
	}
	assert this.boundVars == null || this.boundVars.length == arity() || op instanceof QuanUpdateOperator; //XXX
    }
    
    
    public TermImpl(Operator op, 
	    	    ArrayOfTerm subs, 
	    	    JavaBlock javaBlock, 
	    	    ArrayOfQuantifiableVariable boundVars) {
	assert op != null;
	assert subs != null;
	assert javaBlock != null;
	this.op   = op;
	this.subs = subs.size() == 0 ? EMPTY_TERM_LIST : subs;
	this.javaBlock = javaBlock;
	if(boundVars != null) {
	    this.boundVars = new ArrayOfQuantifiableVariable[subs.size()];
	    for(int i = 0; i < subs.size(); i++) {
		this.boundVars[i] = boundVars;
	    }
	} else {
	    this.boundVars = null;
	}
    }    
    
    
    public TermImpl(Operator op, 
	    	    ArrayOfTerm subs, 
	    	    JavaBlock javaBlock) {
	this(op, subs, javaBlock, (ArrayOfQuantifiableVariable[])null);
    }    

    
    public TermImpl(Operator op, ArrayOfTerm subs) {
	this(op, subs, JavaBlock.EMPTY_JAVABLOCK);
    }


    public TermImpl(Operator op, Term[] subs) {
	this(op, new ArrayOfTerm(subs), JavaBlock.EMPTY_JAVABLOCK);
    }
    
    
    public TermImpl(Operator op) {
	this(op, EMPTY_TERM_LIST);
    }    
    
        
    //-------------------------------------------------------------------------
    //internal methods
    //------------------------------------------------------------------------- 

    private void determineFreeVarsAndMetaVars() {
	freeVars = SetAsListOfQuantifiableVariable.EMPTY_SET;
        metaVars = SetAsListOfMetavariable.EMPTY_SET;
        
        if(op instanceof QuantifiableVariable) {
            freeVars = freeVars.add((QuantifiableVariable) op);
        }else if ( op instanceof Metavariable ) {
            metaVars = metaVars.add ( (Metavariable)op );
        }
        
        for(int i = 0, ar = arity(); i < ar; i++) {
            Term subTerm = sub(i);
	    SetOfQuantifiableVariable subFreeVars = subTerm.freeVars();
	    SetOfMetavariable subMetaVars = subTerm.metaVars();
	    for(int j = 0, sz = varsBoundHere(i).size(); j < sz; j++) {
		subFreeVars 
		    = subFreeVars.remove(varsBoundHere(i)
			         .getQuantifiableVariable(j));
	    }
	    freeVars = freeVars.union(subFreeVars);
	    metaVars = metaVars.union(subMetaVars);
	}
    }
    
    
    
    //-------------------------------------------------------------------------
    //public interface
    //------------------------------------------------------------------------- 
    
    public Operator op() {
        return op;
    }
    
    
    public ArrayOfTerm subs() {
	return subs;
    }
    
    
    public Term sub(int nr) {
	return subs.getTerm(nr);
    }
    
    
    public Term subAt(PosInTerm pos) {
        Term sub = this;
        for (final IntIterator it = pos.iterator(); it.hasNext(); ) {	
            sub = sub.sub(it.next());
        }
        return sub;
    }
   
    
    public JavaBlock javaBlock() {
	return javaBlock;
    }
    
        
    public ArrayOfQuantifiableVariable varsBoundHere(int n) {
	if(boundVars == null || (op instanceof QuanUpdateOperator && n >= boundVars.length)) { //XXX
	    return EMPTY_VAR_LIST;
	} else {
	    return boundVars[n];
	}
    }
    
    
    public Term checked() {
	if(op().validTopLevel(this)) {
	    return this;	    
	} else {	   	    
	    throw new TermCreationException(op(), this);
	}
    }

    
    public int arity() {
	return op.arity();
    }
    
    
    public Sort sort() {
	return op.sort(subs);
    }
    

    public int depth() {
	if(depth == -1) {
            for (int i = 0, sz = arity(); i < sz; i++) {
                final int subTermDepth = sub(i).depth();
                if(subTermDepth > depth) {
                    depth = subTermDepth;   
                }
            }
            depth++;
	}
        return depth;
    }
    
    
    public boolean isRigid() {
	if(rigid == ThreeValuedTruth.UNKNOWN) {
            if(!op.isRigid()) {
        	rigid = ThreeValuedTruth.FALSE;
            } else {
        	rigid = ThreeValuedTruth.TRUE;
        	for(int i = 0, ar = arity(); i < ar; i++) {
            	    if(!sub(i).isRigid ()) {
            		rigid = ThreeValuedTruth.FALSE;
            		break;
            	    }
        	}
            }
        }
            
       return rigid == ThreeValuedTruth.TRUE;
    }
    

    public SetOfQuantifiableVariable freeVars() {
        if(freeVars == null) {
            determineFreeVarsAndMetaVars();
        }
        return freeVars;
    }
    

    public SetOfMetavariable metaVars () {
        if (metaVars == null) {
            determineFreeVarsAndMetaVars();
        }
        return metaVars;
    }
    
    
    public void execPostOrder(Visitor visitor) {
	visitor.subtreeEntered(this);
	for(int i = 0, ar = arity(); i < ar; i++) {
	    sub(i).execPostOrder(visitor);
	}
	visitor.visit(this);
	visitor.subtreeLeft(this);
    }


    public void execPreOrder(Visitor visitor) {
	visitor.subtreeEntered(this);
	visitor.visit(this);
	for (int i = 0, ar = arity(); i < ar; i++) {
	    sub(i).execPreOrder(visitor);
	}
	visitor.subtreeLeft(this);	
    }
    

    public boolean equalsModRenaming(Object o) {
        if(o == this) {
            return true;
        }       
        if (!(o instanceof Term)) {
	    return false;
	}
	final Constraint constraint = Constraint.BOTTOM.unify(this, 
							      (Term) o, 
							      null);

	return constraint == Constraint.BOTTOM;	
    }
    

    /**
     * true if <code>o</code> is syntactically equal to this term
     */
    public boolean equals(Object o) {
	if(o == this) {
	    return true;
	}
	
	if(!(o instanceof Term)) {
	    return false;	
	}
	final Term t = (Term) o;	

	if(!(sort().equals(t.sort()) 
	     && arity() == t.arity()
	     && op().equals(t.op())
	     && subs().equals(t.subs())
	     && javaBlock().equals(t.javaBlock()))) {
	    return false;
	}
	
	for(int i = 0, n = arity(); i < n; i++) {
	    if(!varsBoundHere(i).equals(t.varsBoundHere(i))) {
		return false;
	    }
	}
	
	return true;
    }


    public final int hashCode(){
        if(hashcode == -1) {
            hashcode = 5;
            hashcode = hashcode*17 + sort().hashCode();
            hashcode = hashcode*17 + arity();            
            hashcode = hashcode*17 + op().hashCode();
            hashcode = hashcode*17 + subs().hashCode();            
            hashcode = hashcode*17 + javaBlock().hashCode();
            for(int i = 0, n = arity(); i < n; i++) {
        	hashcode = hashcode*17 + varsBoundHere(i).hashCode();
            }
            
            if(hashcode == 0) {
        	hashcode = 1;
            }
        }
        return hashcode;
    }


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
}
