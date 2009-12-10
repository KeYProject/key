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

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.QuanUpdateOperator;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.util.Debug;


/**
 *
 */
class QuanUpdateTerm extends Term {

    /**
     * contains the subterms of the represented term
     */
    private final ImmutableArray<Term> subTerm;

    /** depth of the term */
    private final int depth;

    private final ImmutableArray<QuantifiableVariable>[] quanUpdateVars;
    
    /** 
     * creates a UpdateTerm
     * @param op the UpdateOperator
     * @param subs an array of Term
     */
    QuanUpdateTerm (QuanUpdateOperator op,
                    Term[] subs,
                    ImmutableArray<QuantifiableVariable>[] quanUpdateVars) {
        super ( op, op.sort ( subs ) );

        this.quanUpdateVars = quanUpdateVars;
        this.subTerm = new ImmutableArray<Term> ( subs );
        
        // move this to <code>QuanUpdateOperator.validTopLevel</code>?
        Debug.assertTrue ( quanUpdateVars.length == op.locationCount () );
        Debug.assertTrue ( subs.length == op.arity () );
        
        int max_depth = -1;
        for (Term sub : subs) {
            if (sub.depth() > max_depth) {
                max_depth = sub.depth();
            }
        }
        depth = max_depth + 1;
        
    }
 
    public JavaBlock executableJavaBlock () {
        return sub ( arity () - 1 ).javaBlock ();
    }

    /** toString */
    public String toString () {
        final QuanUpdateOperator op = (QuanUpdateOperator)op ();
        StringBuffer sb = new StringBuffer ( "{" );
	QuantifiableVariable qvar = null;
        for ( int i = 0; i < op.locationCount (); i++ ) {
	    if(quanUpdateVars[i].size()>0)
              sb.append ( "\\for " );
	    if(quanUpdateVars[i].size() == 1) {
                qvar = quanUpdateVars[i].get(0);
		if(qvar instanceof LogicVariable) {
		  sb.append (qvar.sort()+" "+ qvar.name());
		}else{
                  sb.append (qvar);
		}
	        sb.append ( "; " );
	    }else{
	      for(int j=0;j<quanUpdateVars[i].size();j++) {
                if(j==0)
	          sb.append("(");
		qvar = quanUpdateVars[i].get(j);
		if(qvar instanceof LogicVariable) {
		  sb.append (qvar.sort()+" "+ qvar.name());
		}else{
                  sb.append (qvar);
		}
		if(j<quanUpdateVars[i].size()-1)
		  sb.append("; ");
		else
	          sb.append(")");
	      }
	    }
            if ( op.guardExists ( i ) ) {
                sb.append ( "\\if (" );
                sb.append ( sub ( op.guardPos ( i ) ) );
                sb.append ( ") " );
            }
            sb.append ( op.location ( this, i ) );
            sb.append ( ":=" );
            sb.append ( op.value ( this, i ) );
            if ( i < op.locationCount () - 1 ) {
                sb.append ( " || " );
            }
        }
        sb.append ( "}" );
        sb.append ( sub ( arity () - 1 ) );
        return sb.toString ();
    }

    private ImmutableArray<QuantifiableVariable>[] boundVarsCache = null;
    
    /* (non-Javadoc)
     * @see de.uka.ilkd.key.logic.Term#varsBoundHere(int)
     */
    public ImmutableArray<QuantifiableVariable> varsBoundHere (int n) {
        if ( n >= arity () - 1 ) return new ImmutableArray<QuantifiableVariable> ();

        if ( boundVarsCache == null ) {
            boundVarsCache = new ImmutableArray [arity () - 1];

            final QuanUpdateOperator thisOp = (QuanUpdateOperator)op ();
            for ( int i = 0; i != thisOp.locationCount (); ++i ) {
                for ( int j = thisOp.entryBegin ( i ), end = thisOp.entryEnd ( i );
                      j != end;
                      ++j ) {
                    boundVarsCache[j] = quanUpdateVars[i];
                }
            }
        }

        return boundVarsCache[n];
    }    

    /* (non-Javadoc)
     * @see de.uka.ilkd.key.logic.Term#arity()
     */
    public int arity () {
        return subTerm.size();
    }
    
    /* (non-Javadoc)
     * @see de.uka.ilkd.key.logic.Term#depth()
     */
    public int depth () {
        return depth;
    }
    
    /* (non-Javadoc)
     * @see de.uka.ilkd.key.logic.Term#sub(int)
     */
    public Term sub (int nr) {
        return subTerm.get ( nr );
    }
}
