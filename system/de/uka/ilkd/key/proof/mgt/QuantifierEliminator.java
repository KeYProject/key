// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof.mgt;

import de.uka.ilkd.key.logic.ClashFreeSubst;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.MethodSpecTransformation;
import de.uka.ilkd.key.util.Debug;


/**
 * Pre-processor for <code>MethodSpecTransformation</code>.
 * Pull out quantifiers from a formula, only leaving over subformulas of the
 * shape <code>all x. f@pre(...) = t</code> (such subformulas are removed by
 * <code>MethodSpecTransformation</code>).
 */
public class QuantifierEliminator {
    
    private final static TermFactory tf = TermFactory.DEFAULT;
    
    private ListOfQuantifierPrefixEntry quantifiers;
    private Term quantifierFreeFormula;
    
    private QuantifierEliminator subFormulas[];
    private final Term formula;
    
    private ListOfQuantifierPrefixEntry createQuantifierList () {
        ListOfQuantifierPrefixEntry list = SLListOfQuantifierPrefixEntry.EMPTY_LIST;
        for ( int i = 0; i != formula.arity (); ++i )
            list = list.prepend ( subFormulas[i].getQuantifiers () );
        return list;
    }
    
    private Term createQuantifierFreeFormula() {
        final Term[] subs = new Term[formula.arity()];
        for (int i = 0; i != formula.arity(); ++i)
            subs[i] = subFormulas[i].getQuantifierFreeFormula();
            
        return tf.createTerm ( op (),
                               subs,
                               formula.varsBoundHere ( 0 ),
                               formula.javaBlock () );
    }
    
    public static QuantifierEliminator create (Term f) {
        if ( f.op () == Op.EQV ) {
            // handle equivalences by rewriting them using simpler junctors
            // could be made more efficiently: check whether there are really
            // bound variables within the formula
            final Term s0 = f.sub ( 0 );
            final Term s1 = f.sub ( 1 );
            final Term ns0 = tf.createJunctorTerm ( Op.NOT, s0 );
            final Term ns1 = tf.createJunctorTerm ( Op.NOT, s1 );
            final Term simplerF =
                tf.createJunctorTerm ( Op.OR,
                                       tf.createJunctorTerm ( Op.AND, s0, s1 ),
                                       tf.createJunctorTerm ( Op.AND, ns0, ns1 ) );
            return create ( simplerF );
        }
        
        return new QuantifierEliminator ( f );
    }
    
    private QuantifierEliminator (Term f) {
        formula = f;
        
        if ( formula.sort () != Sort.FORMULA ) {
            // it is assumed that no variables are bound within terms
            quantifiers = SLListOfQuantifierPrefixEntry.EMPTY_LIST;
            quantifierFreeFormula = formula;
            return;
        }
        
        subFormulas = new QuantifierEliminator [formula.arity ()];
        for ( int i = 0; i != formula.arity (); ++i )
            subFormulas[i] = QuantifierEliminator.create ( formula.sub ( i ) );
        
        handleDifferentOps ();

        // make some memory reclaimable
        subFormulas = null;
    }
    
    private void handleDifferentOps () {
        if ( opIs ( Op.ALL ) || opIs ( Op.EX ) ) {
            handleQuantifier ();
        } else if ( opIs ( Op.NOT ) ) {
            quantifiers = QuantifierPrefixEntry.invert ( subFormulas[0].getQuantifiers () );
            quantifierFreeFormula = createQuantifierFreeFormula ();
        } else if ( opIs ( Op.AND ) || opIs ( Op.OR ) || opIs ( Op.DIA )
                    || opIs ( Op.BOX ) || opIs ( Op.TRUE ) || opIs ( Op.FALSE )
                    || op () instanceof Function || opIs ( Op.EQUALS ) ) {
            quantifiers = createQuantifierList ();
            quantifierFreeFormula = createQuantifierFreeFormula ();
        } else if ( opIs ( Op.IMP ) ) {
            final ListOfQuantifierPrefixEntry firstList =
                QuantifierPrefixEntry.invert ( subFormulas[0].getQuantifiers () );
            quantifiers = firstList.prepend ( subFormulas[1].getQuantifiers () );
            quantifierFreeFormula = createQuantifierFreeFormula ();
        } else {
            Debug.fail ( "QuantifierEliminator: Don't know what to do with "
                         + formula );
        }
    }

    private boolean opIs (Op op) {
        return op () == op;
    }

    private Operator op () {
        return formula.op ();
    }

    private void handleQuantifier () {
        if ( MethodSpecTransformation.isAtPreDefinition ( formula ) ) {
            quantifiers = SLListOfQuantifierPrefixEntry.EMPTY_LIST;
            quantifierFreeFormula = formula;
            return;
        }
        
        final QuantifiableVariable oriVar =
            formula.varsBoundHere ( 0 ).getQuantifiableVariable ( 0 );
        // defensively create a new variable
        final LogicVariable newVar =
            new LogicVariable ( oriVar.name (), oriVar.sort () );
        final ClashFreeSubst subst =
            new ClashFreeSubst ( oriVar, tf.createVariableTerm ( newVar ) );
        quantifierFreeFormula = subst.apply ( subFormulas[0].getQuantifierFreeFormula () );
        
        final QuantifierPrefixEntry entry =
            new QuantifierPrefixEntry ( newVar,
                                        opIs (Op.ALL) );
        quantifiers = subFormulas[0].getQuantifiers ().prepend ( entry );
    }

    /**
     * @return Returns the quantifierFreeFormula.
     */
    public Term getQuantifierFreeFormula () {
        return quantifierFreeFormula;
    }
    
    /**
     * @return Returns the quantifiers.
     */
    public ListOfQuantifierPrefixEntry getQuantifiers () {
        return quantifiers;
    }
}
