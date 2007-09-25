// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.rule.soundness;

import de.uka.ilkd.key.logic.IteratorOfConstrainedFormula;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Op;
import de.uka.ilkd.key.rule.*;

/**
 * Build the meaning formula for a given taclet
 */
public class MeaningFormulaBuilder {
    
    private final TacletApp app;

    public MeaningFormulaBuilder ( TacletApp p_app ) {
	app = p_app;
    }

    public Term build () {
    	checkTaclet ();
    	return createMF ();
    }

    /**
     * Ensure that we are really able to cope with the
     * given taclet (incomplete)
     */
    private void checkTaclet () {
    	if ( isRewriteTacletWithRWorAdd () &&
    	     !(((RewriteTaclet)getTaclet()).getStateRestriction() == RewriteTaclet.SAME_UPDATE_LEVEL) )
	    throw new IllegalArgumentException
	        ( "Can't handle rewrite taclets " +
                  "without the \"\\sameUpdateLevel\" flag\n" +
                  "and with if- or add-parts" );
        
        if ( getTaclet().varsNewDependingOn().hasNext() )
	    throw new IllegalArgumentException
		( "Can't handle taclets " +
		  "with a \"new depending on\" variable condition" );
		  
	if ( getTaclet().getVariableConditions().hasNext () )
	    throw new IllegalArgumentException
	  	( "Can't handle taclets " +
	          "with a generic variable condition" );
    }

    /**
     * @return true iff the treated taclet is a rewrite taclet that has an
     *         non-empty if-part or a non-empty add-part
     */
    private boolean isRewriteTacletWithRWorAdd () {
        if ( !isRewriteTaclet () ) return false;
        
        if ( ( (RewriteTaclet)getTaclet () ).ifSequent () != Sequent.EMPTY_SEQUENT )
            return true;

        final IteratorOfTacletGoalTemplate it =
            getTaclet ().goalTemplates ().iterator ();
            
        while ( it.hasNext () ) {
            if ( it.next().sequent () != Sequent.EMPTY_SEQUENT ) return true;
        }

        return false;
    }

    private Term createMF () {
    	return Imp ( createPremisses(), createConclusion () );
    }

    private Term createConclusion() {
    	final Term ifPart = createMF ( getTaclet ().ifSequent() );
    	
        if ( isFindTaclet () && !isRewriteTaclet() ) {
            if ( isAntecTaclet() )
                return Imp ( getFind (), ifPart );
	    else
                return Or ( getFind (), ifPart );
        }

        return ifPart;            
    }

    private Term createPremisses() {
        Term res = True ();
    	final IteratorOfTacletGoalTemplate it =
    	    getTaclet ().goalTemplates().iterator ();
    	    
    	while ( it.hasNext () )
    	    res = And ( res, createMF ( it.next () ) );
    	    
    	return res;
    }

    private Term createMF ( TacletGoalTemplate p ){
    	final Term addPart = createMF ( p.sequent () );
    	
    	if ( isFindTaclet () ) {
    	    if ( isRewriteTaclet () ) {
    	    	if ( p instanceof RewriteTacletGoalTemplate ) {
    	    	    final Term rwPart = createRWPartRewrite
    	    	        ( (RewriteTacletGoalTemplate)p );
    	    	    return Imp ( rwPart, addPart );
    	    	}
    	    } else {
    	    	if ( p instanceof AntecSuccTacletGoalTemplate ) {
		    final Term rwPart = createMF
		        ( ((AntecSuccTacletGoalTemplate)p).replaceWith() );
		    return Or ( rwPart, addPart );
    	    	}
    	    }
    	}
    	
    	return addPart;
    }

    private Term createRWPartRewrite ( RewriteTacletGoalTemplate p ) {
    	final Equality eq = getFind ().sort ().getEqualitySymbol();
    	return getTF ().createEqualityTerm(eq, getFind (), p.replaceWith() );
    }

    private Term createMF ( Sequent p ){
	Term antec = True ();
	IteratorOfConstrainedFormula it = p.antecedent().iterator ();
    	
	while ( it.hasNext () )
	    antec = And ( antec, it.next ().formula () );

	Term succ = False ();
	it = p.succedent().iterator ();
    	
	while ( it.hasNext () )
	    succ = Or ( succ, it.next ().formula () );

	return Imp ( antec, succ );
    }

    private Term And ( Term p0, Term p1 ) {
	return getTF ().createJunctorTermAndSimplify ( Op.AND, p0, p1 );
    }

    private Term Or ( Term p0, Term p1 ) {
	return getTF ().createJunctorTermAndSimplify ( Op.OR, p0, p1 );
    }

    private Term Imp ( Term p0, Term p1 ) {
	return getTF ().createJunctorTermAndSimplify ( Op.IMP, p0, p1 );
    }

    private Term True () {
    	return getTF ().createJunctorTerm(Op.TRUE);
    }

    private Term False () {
	return getTF ().createJunctorTerm(Op.FALSE);
    }

    private boolean isFindTaclet() {
        return getTaclet() instanceof FindTaclet;
    }

    private boolean isAntecTaclet() {
        return getTaclet() instanceof AntecTaclet;
    }

    private boolean isRewriteTaclet() {
	return getTaclet() instanceof RewriteTaclet;
    }

    private TacletApp getTacletApp() {
        return app;
    }

    private Taclet getTaclet() {
	return getTacletApp().taclet ();
    }

    private Term getFind() {
	if ( isFindTaclet() )
	    return ((FindTaclet)getTaclet()).find ();
	return null;
    }

    private TermFactory getTF() {
        return TermFactory.DEFAULT;
    }

}
