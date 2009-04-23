// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.strategy;

import de.uka.ilkd.key.logic.ConstrainedFormula;
import de.uka.ilkd.key.logic.FormulaChangeInfo;
import de.uka.ilkd.key.logic.ListOfFormulaChangeInfo;
import de.uka.ilkd.key.logic.PIOPathIterator;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IUpdateOperator;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.proof.FormulaTag;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.util.Debug;

/**
 * Instances of this class are immutable
 */
public class FindTacletAppContainer extends TacletAppContainer {

    /**
     * The position of the rule app in two different representations:
     * <code>positionTag</code> denotes the concerned formula and survives
     * modifications of the sequent and of parts of the formula, and
     * <code>applicationPosition</code> is the original position for which the
     * rule app was created
     */
    private final FormulaTag      positionTag;
    private final PosInOccurrence applicationPosition;

    FindTacletAppContainer ( RuleApp         p_app,
			     PosInOccurrence p_pio,
			     RuleAppCost     p_cost,
			     Goal            p_goal,
                             long            p_age ) {
	super ( p_app, p_cost, p_age );
    	applicationPosition = p_pio;
    	positionTag         =
    	    p_goal.getFormulaTagManager().getTagForPos(p_pio.topLevel());

        if ( positionTag == null )
            // faster than <code>assertFalse</code>
            Debug.fail ( "Formula " + p_pio + " does not exist" );
    }


    /**
     * @return true iff the stored rule app is applicable for the given sequent,
     * i.e. if the find-position does still exist (if-formulas are not
     * considered)
     */
    protected boolean isStillApplicable ( Goal p_goal ) {
    	final PosInOccurrence topPos =
    	    p_goal.getFormulaTagManager().getPosForTag(positionTag);
	if ( topPos == null )
	    // the formula does not exist anymore, bail out
	    return false;
	if ( !topPos.constrainedFormula().constraint().equals
	     ( applicationPosition.constrainedFormula().constraint() ) )
	    // the constraint of the formula has changed, bail out
	    return false;
	if ( subformulaOrPreceedingUpdateHasChanged ( p_goal ) )
	    return false;
	return true;
    }


    /**
     * @return true iff a subformula that contains the find position stored by
     * this object has been altered since the creation of this object or if a 
     * preceeding update has changed
     */
    private boolean subformulaOrPreceedingUpdateHasChanged ( Goal p_goal ) {
    	ListOfFormulaChangeInfo infoList =
    	    p_goal.getFormulaTagManager().getModifications(positionTag);

	while ( !infoList.isEmpty () ) {
	    final FormulaChangeInfo info = infoList.head ();
	    infoList = infoList.tail ();
	    
	    final ConstrainedFormula newFormula = info.getNewFormula();
        if ( newFormula == applicationPosition.constrainedFormula() )
            // then there were no relevant modifications since the creation
            // of the rule app object
            return false;

	    if ( !independentSubformulas ( info.getPositionOfModification(),
	                                   newFormula ) )
	        return true;
	}
	
	return false;
    }


    /**
     * checks if the modification path and the postition where this taclet application
     * has been matched again denote independant subformulas. The modification affects 
     * a formula <code>F</code> if <code>F</code> is a subformula of the modified one 
     * or the modification took part inside an update which may occur in the update 
     * prefix instantiation of the taclet application    
     * @return true iff <code>applicationPosition</code> is in the scope of
     * the position <code>p_pos</code> (the formulas are not compared, only the
     * positions within the formulas) and no indirect relationship exists which 
     * is established by a modification that occurred inside an update 
     */
    private boolean independentSubformulas(PosInOccurrence changePos,
                                           ConstrainedFormula newFormula) {
        final PIOPathIterator changePIO = changePos.iterator ();
        final PIOPathIterator appPIO = applicationPosition.iterator ();

        while ( true ) {
            final int changeIndex = changePIO.next ();
            final int appIndex = appPIO.next ();

            if ( appIndex == -1 ) return false;
            
            if ( changeIndex == -1 ) {
                final Term beforeChangeTerm = changePIO.getSubTerm ();
                final Operator beforeChangeOp = beforeChangeTerm.op ();

                // special case: a taclet application is not affected by changes
                // to a preceding program, as long as the post-condition of the
                // program does not change. this is a pretty common situation
                // during symbolic program execution; also consider
                // <code>TermTacletAppIndex.updateCompleteRebuild</code>
                if ( beforeChangeOp instanceof Modality ) {
                    final PosInOccurrence afterChangePos =
                        changePos.replaceConstrainedFormula ( newFormula );
                    final Term afterChangeTerm = afterChangePos.subTerm ();
                    return beforeChangeOp == afterChangeTerm.op ()
                           && beforeChangeTerm.sub ( 0 )
                              .equals ( afterChangeTerm.sub ( 0 ) );
                }
                
                return false;
            }

            if ( changeIndex != appIndex ) {
                // in case a change within an update occurred, also (some)
                // taclets within the update target expression have to be
                // invalidated
                final Operator modOp = changePIO.getSubTerm ().op ();

                return !( modOp instanceof IUpdateOperator
                          && appIndex == ( (IUpdateOperator)modOp ).targetPos ()
                          && updateContextIsRecorded () );
            }
        }
    }

    /**
     * @return <code>true</code> iff the update context (updates above the
     *         application position) is relevant and stored for this taclet app.
     *         In this case, the taclet app has to be discarded as soon as the
     *         update context changes
     */
    private boolean updateContextIsRecorded() {
        return !getTacletApp ().instantiations ().getUpdateContext ().isEmpty ();
    }

    /**
     * @return non-null for FindTaclets
     */
    protected PosInOccurrence getPosInOccurrence ( Goal p_goal ) {
    	final PosInOccurrence topPos =
    	    p_goal.getFormulaTagManager().getPosForTag(positionTag);

	assert topPos != null;
	
	return applicationPosition.replaceConstrainedFormula
	    ( topPos.constrainedFormula () );
    }

}
