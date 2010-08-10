// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.rule.metaconstruct;

import java.util.Iterator;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.ArraySortImpl;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.UpdateSimplifier;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.rule.updatesimplifier.AssignmentPair;
import de.uka.ilkd.key.rule.updatesimplifier.Update;
import de.uka.ilkd.key.util.Debug;

/* @author Christoph Gladisch
 * This class is necessary for the following rule :
 *     Gamma |- {u'} phi', Delta      Gamma |- {u} phi, u=u' & {u'}phi'<->{u'}phi, Delta
 * ---------------------------------------------------------
 *             Gamma |- {u} phi, Delta
 * 
 * this meta construct generates 
 * u=u' & {u'}phi'<->{u'}phi
 * where
 *  u1=u2  :=  (obl_f1 & obl_f2 & obl_f3 & ... obl_fn)
 * and
 *  obl_fi  :=   \forall x1, x2, ... ; ({u1} fi(x1, x2, ...)) = ({u2} fi(x1, x2, ...))
 *  
 *  This rule allowes to substitute updates by equivalent updates "modulo defindness":
 *  
 */
public class MetaEquivalentUpdates extends AbstractMetaOperator {
	private final static TermFactory tf = TermFactory.DEFAULT;
    private final static TermBuilder tb = TermBuilder.DF;
	private UpdateFactory uf;
	private Services serv;

	public MetaEquivalentUpdates() {
		super(new Name("#equivUpdates"), 2);
	}

    /**
     * Determine the sort that the operator <code>op</code> takes as
     * <code>argNum</code>s argument. Stupid, but class <code>Operator</code>
     * does not provide a nice API to computer this sort ...
     */
    private Sort getArgumentSort(Location op, int argNum) {
        if ( op instanceof AttributeOp ) {
            return ((AttributeOp) op).getContainerType().getSort();
        } else if ( op instanceof ArrayOp ) {
            switch ( argNum ) {
            case 0:
                return ( (ArrayOp)op ).arraySort ();
            case 1:
                return serv.getTypeConverter ().getIntegerLDT ().getNumberSymbol ().sort ();
            }
        } else if ( op instanceof Function ) {
            return ( (Function)op ).argSort ( argNum );
        }

        assert false : "Location " + op + " of class " + op.getClass ()
                       + " is not supported yet";
        return null;
    }
    
	/**	 
	 *   obl_fi  :=   \forall x1, x2, ... ; ({u1} fi(x1, x2, ...)) = ({u2} fi(x1, x2, ...))
     *   This method requires as argument the "location term" t and not just the "location operator" of t
     *   because some operators, e.g. ".length", may have unknown sorts. This caused BUG 0898 resp. 0910.
	 * */
	private Term eqUpdWithRespectToTerm(Update upd1, Update upd2, Term t) {
		final Term[] varArray = new Term[t.arity()];
		//System.out.println("Location as term(" + t.arity() + "):" + t.toString());
		for (int j = 0; j < t.arity(); j++) {
            Sort argSort = getArgumentSort((Location)t.op(), j);
            if(argSort==null){
                //If the sort cannot be determined from the operator, then try to derive
                //the sort from the term arguments
                Term subj = t.sub(j);
                argSort = subj.sort();
                Debug.assertFalse(argSort==null, "Cannot determine sort of argument "+j+
                            " (it is null) of the following term that stemms " +
                            "from left-hand side of an update:"+
                            t.toString());
                    //System.out.println("getArgumentSort(op, "+j+"):null");
            }
			LogicVariable lv = new LogicVariable(new Name("x" + j),argSort);
			Term vt = tf.createVariableTerm(lv);
			//System.out.print(" " + vt.toString());
			varArray[j] = vt;
		}

                final Term locWithVars = tf.createTerm ( t.op(), varArray,
                                                         null,
                                                         JavaBlock.EMPTY_JAVABLOCK );
        		// System.out.println("Term with free variables: " + locWithVars.toString());
        
        	final Term u1t = uf.apply ( upd1, locWithVars );
                final Term u2t = uf.apply ( upd2, locWithVars );
        
                final ImmutableSet<QuantifiableVariable> freeVars = locWithVars.freeVars ();
		return tb.all ( freeVars.toArray (new QuantifiableVariable[freeVars.size()]), tb.equals ( u1t, u2t ) );
	}

    private Location getUpdatedOp(AssignmentPair ap) {
        final Location loc = ap.location();
        if ( loc instanceof ArrayOp
             && loc.sort ().extendsTrans ( getJavaLangObject () ) ) {
            // we return the most general ArrayOp, namely the one for
            // java.lang.Object[]-arrays
            final Sort javaLangCloneable =
                serv.getJavaInfo ().getJavaLangCloneableAsSort ();
            final Sort javaIoSerializable =
                serv.getJavaInfo ().getJavaIoSerializableAsSort ();
            
            return ArrayOp.getArrayOp ( ArraySortImpl.getArraySort (
                             getJavaLangObject (), getJavaLangObject (),
                             javaLangCloneable, javaIoSerializable ) );
        }
        return loc;
    }

    private Sort getJavaLangObject() {
        return serv.getJavaInfo ().getJavaLangObjectAsSort ();
    }

    private ImmutableSet<Term> addLocTermsToSet(Update upd,
                                            ImmutableSet<Term> updatedLocTerms) {
        final ImmutableArray<AssignmentPair> pairs = upd.getAllAssignmentPairs ();
        for ( int i = 0; i < pairs.size (); i++ ) {
            updatedLocTerms = updatedLocTerms.add( pairs.get ( i ).locationAsTerm());
            /* updatedLocs = updatedLocs.add ( getUpdatedOp ( pairs.getAssignmentPair ( i ) ) ); BUG 0898*/
        }
        return updatedLocTerms;
    }

	/** 
	 *  u1=u2  :=  (obl_f1 & obl_f2 & obl_f3 & ... obl_fn)
	 * and
	 *  obl_fi  :=   \forall x1, x2, ... ; ({u1} fi(x1, x2, ...)) = ({u2} fi(x1, x2, ...))
	 */
	private Term eqivalentUpdates(Update upd1, Update upd2) {
        	ImmutableSet<Term> updatedLocTerms = DefaultImmutableSet.<Term>nil();
                
                updatedLocTerms = addLocTermsToSet ( upd1, updatedLocTerms );
                updatedLocTerms = addLocTermsToSet ( upd2, updatedLocTerms );
        
        		// System.out.println("Locations:" + updatedLocs);
        
                Term res = tb.tt ();

        for (Term updatedLocTerm : updatedLocTerms) {
            res = tb.and(res, eqUpdWithRespectToTerm(upd1, upd2,
                    updatedLocTerm));
        }
        
		return res;
	}

	/** {u'}phi<->{u'}phi'*/
	private Term equivalentSubFormulas(Term u1phi1, Term u2phi2) {
        final Update upd2 = Update.createUpdate ( u2phi2 );

        final Term phi1 = getTarget ( u1phi1 );
        final Term phi2 = getTarget ( u2phi2 );

        if ( ( phi1.sort () == Sort.FORMULA ) != ( phi2.sort () == Sort.FORMULA ) )
            return tb.ff ();

        final Term u2phi1 = uf.prepend ( upd2, phi1 );

        if ( phi1.sort () == Sort.FORMULA )
            return tb.equiv ( u2phi1, u2phi2 );
        else
            return tb.equals ( u2phi1, u2phi2 );
    }

    private Term getTarget(Term t) {
        if ( t.op () instanceof IUpdateOperator )
            return ( (IUpdateOperator)t.op () ).target ( t );
        return t;
    }


	/** calculates the resulting term:
	 * u=u' & {u'}phi'<->{u'}phi
	 * where
	 *  u1=u2  :=  (obl_f1 & obl_f2 & obl_f3 & ... obl_fn)
	 * and
	 *  obl_fi  :=   \forall x1, x2, ... ; ({u1} fi(x1, x2, ...)) = ({u2} fi(x1, x2, ...))
	 */
	public Term calculate(Term term, SVInstantiations svInst, Services services) {
		serv = services;
		uf = new UpdateFactory(serv, new UpdateSimplifier ());
		
		final Term u1phi1 = term.sub(0);
		final Term u2phi2 = term.sub(1);
		//System.out.println("u1phi1:" + u1phi1.toString());
		//System.out.println("u2phi2:" + u2phi2.toString());
		final Update upd1 = Update.createUpdate(u1phi1);
		final Update upd2 = Update.createUpdate(u2phi2);
		//System.out.println("upd1:" + upd1.toString());
		//System.out.println("upd2:" + upd2.toString());

		final Term u1EqvU2 = eqivalentUpdates(upd1, upd2);
		//System.out.println("u1EqvU2:" + u1EqvU2.toString());
		final Term phi1EqvPhi2 = equivalentSubFormulas(u1phi1, u2phi2);
		//System.out.println("phi1EqvPhi2:" + phi1EqvPhi2.toString());
		
        serv = null;
        uf = null;
        
		return tb.and ( u1EqvU2, phi1EqvPhi2 );
	}

	public Sort sort(Term[] term) {
		return Sort.FORMULA;
	}

	public boolean validTopLevel(Term term) {
		return term.arity() == arity();
	}

}
