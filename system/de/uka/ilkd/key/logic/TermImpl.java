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

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.logic.op.Metavariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.sort.Sort;


final class TermImpl implements Term {

    private static final ImmutableArray<Term> EMPTY_TERM_LIST 
    	= new ImmutableArray<Term>();
    private static final ImmutableArray<QuantifiableVariable> EMPTY_VAR_LIST
    	= new ImmutableArray<QuantifiableVariable>();

    //content
    private final Operator op;
    private final ImmutableArray<Term> subs;
    private final ImmutableArray<QuantifiableVariable> boundVars;
    private final JavaBlock javaBlock;
    
    //caches
    private static enum ThreeValuedTruth { TRUE, FALSE, UNKNOWN }
    private int depth = -1;
    private ThreeValuedTruth rigid = ThreeValuedTruth.UNKNOWN; 
    private ImmutableSet<QuantifiableVariable> freeVars = null;
    private ImmutableSet<Metavariable> metaVars = null;
    private int hashcode = -1;
    
    
    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------
    
    public TermImpl(Operator op, 
	    	    ImmutableArray<Term> subs, 
	    	    ImmutableArray<QuantifiableVariable> boundVars, 
	    	    JavaBlock javaBlock) {
	assert op != null;
	assert subs != null;
	this.op   = op;
	this.subs = subs.size() == 0 ? EMPTY_TERM_LIST : subs;
	this.boundVars = boundVars == null ? EMPTY_VAR_LIST : boundVars;	
	this.javaBlock = javaBlock == null 
	                 ? JavaBlock.EMPTY_JAVABLOCK 
	                 : javaBlock;
    }
    

        
    //-------------------------------------------------------------------------
    //internal methods
    //------------------------------------------------------------------------- 
    
    private void determineFreeVarsAndMetaVars() {
	freeVars = DefaultImmutableSet.<QuantifiableVariable>nil();
        metaVars = DefaultImmutableSet.<Metavariable>nil();
        
        if(op instanceof QuantifiableVariable) {
            freeVars = freeVars.add((QuantifiableVariable) op);
        } else if(op instanceof Metavariable) {
            metaVars = metaVars.add((Metavariable) op);
        }
        for(int i = 0, ar = arity(); i < ar; i++) {
	    ImmutableSet<QuantifiableVariable> subFreeVars = sub(i).freeVars();
	    for(int j = 0, sz = varsBoundHere(i).size(); j < sz; j++) {
		subFreeVars = subFreeVars.remove(varsBoundHere(i).get(j));
	    }
	    freeVars = freeVars.union(subFreeVars);
	    metaVars = metaVars.union(sub(i).metaVars());
	}
    }
    
    
    
    
    //-------------------------------------------------------------------------
    //public interface
    //------------------------------------------------------------------------- 
    
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
        for(final IntIterator it = pos.iterator(); it.hasNext(); ) {	
            sub = sub.sub(it.next());
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
    public Term checked() {
	if(op().validTopLevel(this)) {
	    return this;	    
	} else {	   	    
	    throw new TermCreationException(op(), this);
	}
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
            determineFreeVarsAndMetaVars();
        }
        return freeVars;
    }
    

    @Override
    public ImmutableSet<Metavariable> metaVars() {
	if(metaVars == null) {
	    determineFreeVarsAndMetaVars();
	}
	return metaVars;
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
	final Constraint constraint = Constraint.BOTTOM.unify(this, 
							      (Term) o, 
							      null);

	return constraint == Constraint.BOTTOM;	
    }
    

    /**
     * true if <code>o</code> is syntactically equal to this term
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
}
