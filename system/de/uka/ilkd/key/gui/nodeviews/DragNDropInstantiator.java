// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License.
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.gui.nodeviews;

import java.awt.Point;
import java.awt.datatransfer.Transferable;
import java.awt.datatransfer.UnsupportedFlavorException;
import java.awt.dnd.DropTargetAdapter;
import java.awt.dnd.DropTargetDragEvent;
import java.awt.dnd.DropTargetDropEvent;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.io.IOException;

import javax.swing.JPopupMenu;

import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Constraint;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.rule.*;
import de.uka.ilkd.key.rule.inst.IllegalInstantiationException;

/**
 * <p>
 * The DragNDropInstantiator interpretes drag'n drop actions as taclet
 * instantiations. The behaviour is described below (excluding some
 * "optimisation" details)
 * </p>
 * <p>
 * Let "source" denote the formula/term which is dragged and dropped on another
 * term called "target". The DragNDropInstantiation of a taclet "t" is now
 * defined as follows:
 * <ol>
 * <li>t must have exactly one formula/term in the <tt>find</tt> part and
 * <tt>assumes</tt> sequent (in particular it must have an <tt>assumes</tt> -part)
 * </li>
 * <li>and
 * <ol>
 * <li>if t's goal descriptions do not contain any <tt>replacewith</tt> then
 * "source" is matched against the <tt>find</tt> part of the taclet and
 * "target" has to match the "if" part.</li>
 * <li>if t's goal descriptions contain at least <em>one</em> replacewith
 * then "target" is matched against the <tt>find</tt> part and "source"
 * against the <tt>assumes</tt> part</li>*
 * </ol>
 * or
 * <li>t must have a <tt>find</tt> part, no <tt>assumes</tt> and at least one
 * addrule. In this case source is merged against <tt>find</tt> part and
 * target has to be the complete sequent. Dropping on the sequent arrow is
 * interpreted as applying an addrule(treats hide rules)</li>
 * </ol>
 * The DragNDropInstantiator now determines all taclets, which have a valid
 * drag'n drop instantiation for a given (source, target) position pair. If
 * there is only one taclet with a valid dnd-instantiation this one is executed
 * otherwise the user is presented a list of possible taclets from which she/he
 * can select one.
 * </p>
 */
public class DragNDropInstantiator extends DropTargetAdapter {

    /** the sequentview where dnd has been initiated */
    private SequentView seqView;
    
    
    DragNDropInstantiator(SequentView seqView) {
        this.seqView = seqView;
    }

    public void drop(DropTargetDropEvent event) {


        Point dropLocation = event.getLocation();

        try {
            Transferable transferable = event.getTransferable();
            if (transferable
                    .isDataFlavorSupported(PosInSequentTransferable.POS_IN_SEQUENT_TRANSFER)) {
                interpreteDragAndDropInstantiation(event, dropLocation,
                        transferable);
            } else {
                event.rejectDrop();
            }
        } catch (IOException exception) {
            // just reject drop do not bother the user
            event.rejectDrop();
        } catch (UnsupportedFlavorException ufException) {
            // just reject drop do not bother the user
            event.rejectDrop();
        }

        seqView.requestFocus();
    }

    public void dragOver(DropTargetDragEvent dtde) {       
        seqView.autoscroll(dtde.getLocation());                                          
        seqView.paintHighlights(dtde.getLocation());
    }

    /**
     * Interpretes the drag and drop gesture. Checks which taclets could be
     * meant by the drag'n drop and applies if the app can be uniquely
     * determined, otherwise a selection menu is presented to the user
     */
    private void interpreteDragAndDropInstantiation(DropTargetDropEvent event,
            Point dropLocation, Transferable transferable)
            throws UnsupportedFlavorException, IOException {

        final PosInSequent sourcePos = (PosInSequent) transferable
                .getTransferData(PosInSequentTransferable.POS_IN_SEQUENT_TRANSFER);

        final PosInSequent targetPos = seqView.getPosInSequent(dropLocation);

        if (targetPos == null
                || sourcePos == null
                || sourcePos.isSequent() ) {
            event.rejectDrop();
            return;
        }
             
        final Services services = seqView.mediator().getServices();

        ListOfPosTacletApp applicableApps = 
            getAllApplicableApps(sourcePos, targetPos, services);        
               
        
        if (applicableApps.isEmpty() && !targetPos.isSequent() &&
                targetPos.getPosInOccurrence().posInTerm() != PosInTerm.TOP_LEVEL) {
            // if no applicable taclet is found we relax the target position a bit
            applicableApps = 
                getAllApplicableApps(sourcePos, 
                        PosInSequent.createCfmaPos(targetPos.getPosInOccurrence().up()), 
                        services);
        } 

        // in case of an equal source and target position the selection list is shown 
        // even if only one rule is applicable in order to avoid an accidently 
        // rule appliciation of replace_knwon_* rules and entering
        // the hell of non-confluence..       
        final boolean equalTargetPosition = sourcePos.getPosInOccurrence().equals(
                targetPos.getPosInOccurrence());
        
        if (!equalTargetPosition && applicableApps.size() == 1) {
            execute(applicableApps.head());      
        } else if (applicableApps.size() >= 1) {
            // open a pop up menu for user selection
            SimpleTacletSelectionMenu menu = new SimpleTacletSelectionMenu(
                    applicableApps, seqView.mediator().getNotationInfo(),
                    new PopupListener());

            JPopupMenu pm = menu.getPopupMenu();
            pm.show(seqView, (int) dropLocation.getX(), (int) dropLocation
                    .getY());
        } else {
            // no rule applicable
            event.rejectDrop();
            return;
        }
        event.getDropTargetContext().dropComplete(true);
    }

    /**
     * retrieves all drag'n drop instantiable taclet applications
     * @param sourcePos the PosInSequent where the drag started
     * @param targetPos the PosInSequent where the drop occured     
     * @param services theServices providing access to the program model  
     * @return all drag'n drop instantiable taclet applications
     */
    private ListOfPosTacletApp getAllApplicableApps(final PosInSequent sourcePos, 
            final PosInSequent targetPos, final Services services) {        
        final Sequent sequent = 
            seqView.mediator().getSelectedGoal().sequent();
        
        final Constraint userConstraint = seqView.mediator()
                .getUserConstraint().getConstraint();
        ListOfPosTacletApp applicableApps = SLListOfPosTacletApp.EMPTY_LIST;
        if (targetPos.isSequent()) {
            // collects all applicable taclets at the source position
            // which have an addrule section
            applicableApps = applicableApps.prepend(completeIfInstantiations(
                    getApplicableTaclets(sourcePos,
                            TacletFilter.TACLET_WITH_NO_IF_FIND_AND_ADDRULE),
                    sequent, targetPos.getPosInOccurrence(), userConstraint,
                    services));
        } else {
            if (ProofSettings.DEFAULT_SETTINGS.getGeneralSettings().isDndDirectionSensitive()) {
                applicableApps = applicableApps.prepend(getDirectionDependentApps(sourcePos, targetPos, services, 
                    sequent, userConstraint));
            } else {
                applicableApps = applicableApps.
                    prepend(getDirectionIndependentApps(sourcePos, targetPos, services, 
                        sequent, userConstraint));                
            }         
        }
        return applicableApps;
    }

    /**
     * returns all applicable apps respecting direction information in drag an drop 
     * @param sourcePos PosInSequent where the drag gesture started
     * @param targetPos PosInSequent where the drop action took place
     * @param services the Services
     * @param sequent the Sequent 
     * @param userConstraint the user Constraint 
     * @return  all applicable apps respecting direction information in drag an drop
     */
    private ListOfPosTacletApp getDirectionDependentApps(final PosInSequent sourcePos, 
            final PosInSequent targetPos, final Services services,
            final Sequent sequent, final Constraint userConstraint) {
        
        ListOfPosTacletApp applicableApps = SLListOfPosTacletApp.EMPTY_LIST;
        // all applicable taclets where the drag source has been interpreted
        // as
        // the find part and the drop position as the one of the
        // in this case only taclets with no replacewith part are considered
        applicableApps = applicableApps
                .prepend(completeIfInstantiations(
                        getApplicableTaclets(
                                sourcePos,
                                TacletFilter.TACLET_WITH_IF_FIND_AND_NO_REPLACEWITH),
                        sequent, targetPos.getPosInOccurrence(),
                        userConstraint, services));

        // switch source and target interpretation
        // source is now the "If" instantiation and target the one of the
        // find part in this case only the taclets with at least one
        // replacewith part are considered
        applicableApps = applicableApps.prepend(completeIfInstantiations(
                getApplicableTaclets(targetPos,
                        TacletFilter.TACLET_WITH_IF_FIND_AND_REPLACEWITH),
                sequent, sourcePos.getPosInOccurrence(), userConstraint,
                services));
        
        // get those without an if sequent, in these we will try to apply this rule
        // if: * one sv instantiation is missing
        //     * the term dropped on is a legal instantiation for this sv
        applicableApps = applicableApps.prepend(completeInstantiations(
                getApplicableTaclets(sourcePos,
                        TacletFilter.TACLET_WITH_NO_IF),
                        targetPos.getPosInOccurrence(),
                        services));
        
        return applicableApps;
    }
    
    /**
     * returns all applicable apps without 
     * respecting direction information in drag an drop 
     * @param sourcePos PosInSequent where the drag gesture started
     * @param targetPos PosInSequent where the drop action took place
     * @param services the Services
     * @param sequent the Sequent 
     * @param userConstraint the user Constraint 
     * @return  all applicable apps respecting direction information in drag an drop
     */
    private ListOfPosTacletApp getDirectionIndependentApps(PosInSequent sourcePos, 
            PosInSequent targetPos, final Services services,
            final Sequent sequent, final Constraint userConstraint) {
        
        ListOfPosTacletApp applicableApps = SLListOfPosTacletApp.EMPTY_LIST;

        applicableApps = getDirectionDependentApps(sourcePos, targetPos, services, 
                sequent, userConstraint).
                prepend(getDirectionDependentApps(targetPos, sourcePos, services, 
                        sequent, userConstraint));
        
        return applicableApps;
    }


    /**
     * retrieves all taclets applicable on the given position and select those
     * that fulfill the given filter condition. The filter selects taclets
     * satisfying certain syntactic categories (for example, taclets with at
     * least one replacewith in their goal description or those without any
     * replacewith).
     * 
     * @param findPos
     *            the PosInSequent specifying the formula/term that has to be
     *            matched by the find part of a taclet
     * @param filter
     *            the TacletFilter specifying syntactic restrictions on the
     *            taclets to be returned
     * @return the list of taclets which match the term at the given position
     *         and satisfy the filter condition
     */
    private ListOfPosTacletApp getApplicableTaclets(PosInSequent findPos,
            TacletFilter filter) {

        if (findPos == null || findPos.isSequent()) {
            return SLListOfPosTacletApp.EMPTY_LIST;
        }

        ListOfTacletApp allTacletsAtFindPosition = SLListOfTacletApp.EMPTY_LIST;

        final IteratorOfTacletApp it = seqView.mediator()
                .getFindTaclet(findPos).iterator();
        // if in replaceWithMode only apps that contain at least one replacewith
        // are collected. Otherwise only those without a replacewith.
        while (it.hasNext()) {
            final TacletApp app = it.next();
            if (filter.satisfiesFilterCondition(app.taclet())) {
                allTacletsAtFindPosition = allTacletsAtFindPosition
                        .prepend(app);
            }
        }

        return addPositionInformation(allTacletsAtFindPosition, findPos
                .getPosInOccurrence());
    }

    /**
     * the taclet applications is given the correct position information where
     * their "find" has been matched
     * 
     * @param tacletApps
     *            the ListOfTacletApp with taclet applications to be enriched by
     *            position information
     * @param findPos
     *            the PosInOccurrence against which the find part has been
     *            matched
     * @return the taclet apps as given in <tt>tacletApps</tt> but with
     *         position information
     */
    private ListOfPosTacletApp addPositionInformation(
            ListOfTacletApp tacletApps, PosInOccurrence findPos) {

        ListOfPosTacletApp applicableApps = SLListOfPosTacletApp.EMPTY_LIST;
        IteratorOfTacletApp it = tacletApps.iterator();
        while (it.hasNext()) {
            TacletApp app = it.next();
            if (app instanceof NoPosTacletApp) {
                app = PosTacletApp.createPosTacletApp(
                        (FindTaclet) app.taclet(), app.matchConditions(),
                        findPos);
            }
            applicableApps = applicableApps.prepend((PosTacletApp) app);
        }
        return applicableApps;
    }

    /**
     * tries to complete the (partial) taclet instantantiation of the
     * applications given in <tt>apps</tt>. The resulting applications are
     * returned. The given apps must have either all an if part or none of them.
     * 
     * @param apps
     *            the ListOfPosTacletApp with all apps whose if sequent has to
     *            be matched against the formula specified by the pair
     *            <tt>seq</tt> and <tt>ifPIO</tt>
     * @param seq
     *            the Sequent to which the position information in <tt>ifPIO<tt>
     * is relative to
     * @param ifPIO the PosInOccurrence describing the position of the term to 
     * be matched against the if sequent of the taclets
     * @param userConstraint the Constraint describing user instantiations of
     * metavariables
     * @param services the Services 
     * @return the ListOfPosTacletApp that have been matched successfully
     */
    private ListOfPosTacletApp completeIfInstantiations(ListOfPosTacletApp apps,
            Sequent seq, PosInOccurrence ifPIO, Constraint userConstraint,
            Services services) {

        ListOfPosTacletApp result = SLListOfPosTacletApp.EMPTY_LIST;

        final ListOfIfFormulaInstantiation ifFmlInst;
              
        if (ifPIO == null || !ifPIO.isTopLevel()) {
            // if formula have to be top level formulas
            // TODO: should update prefix be allowed?
            ifFmlInst = null;
        } else {          
            final IfFormulaInstSeq ifInst = new IfFormulaInstSeq(seq,
	        ifPIO.isInAntec(), ifPIO.constrainedFormula());
            ifFmlInst = SLListOfIfFormulaInstantiation.EMPTY_LIST
                    .prepend(ifInst);
        }

        final IteratorOfPosTacletApp it = apps.iterator();
        while (it.hasNext()) {
            PosTacletApp app = it.next();

            final Sequent ifSequent = app.taclet().ifSequent();
            if (ifSequent != null && !ifSequent.isEmpty()) {
                if (ifSequent.size() != 1) {
                  // currently dnd is only supported for taclets with exact one formula
                  // in the if sequent
                  app = null;  
                } else if (ifFmlInst == null) {
                    // as either all taclets have an if sequent or none
                    // we can exit here
                    return SLListOfPosTacletApp.EMPTY_LIST;
                } else {    
                    // the right side is not checked in tacletapp
                    // not sure where to incorporate the check...
                    if (((IfFormulaInstSeq)ifFmlInst.head()).inAntec() == 
                         (ifSequent.succedent().size() == 0)) {        	    
                        app = (PosTacletApp) app.setIfFormulaInstantiations(
                                ifFmlInst, services, userConstraint);
                    }
                }
            }
            if (app != null && app.complete()) {
                //allow use of sufficientlyComplete here?
                result = result.prepend(app);
            }
        }
        return result;
    }

    
    /**
     * tries to complete the (partial) taclet instantantiation of the
     * applications given in <tt>apps</tt>. The resulting applications are
     * returned. 
     * 
     * @param apps
     *            the ListOfPosTacletApp with all apps whose if sequent has to
     *            be matched against the formula specified by the pair
     *            <tt>seq</tt> and <tt>ifPIO</tt>
     * is relative to
     * @param missingSVPIO the PosInOccurrence describing the position of the term an 
     * uninstantiated SV will be matched against 
     * @param services the Services 
     * @return the ListOfPosTacletApp that have been matched successfully
     */
    private ListOfPosTacletApp completeInstantiations(ListOfPosTacletApp apps,
             PosInOccurrence missingSVPIO, Services services) {

        ListOfPosTacletApp result = SLListOfPosTacletApp.EMPTY_LIST;
        if (missingSVPIO == null) {        
            return SLListOfPosTacletApp.EMPTY_LIST; 
        }
        
        final IteratorOfPosTacletApp it = apps.iterator();
        while (it.hasNext()) {
            PosTacletApp app = it.next();
            
            final SchemaVariable missingSV;
            final Sequent ifSequent = app.taclet().ifSequent();
            
            if ((ifSequent != null && !ifSequent.isEmpty()) ||
                    app.uninstantiatedVars().size() != 1) {
               continue;
            } else {
                missingSV = app.uninstantiatedVars().iterator().next();
            }            
	    try {
		app = (PosTacletApp)app.addCheckedInstantiation(missingSV, 
                      missingSVPIO.subTerm(), services, true);
	    } catch (IllegalInstantiationException ie) {
		app = null;
	    }
            
            if (app != null && app.sufficientlyComplete()) {
                result = result.prepend(app);
            }
        }
        return result;
    }

    
    /**
     * applies the given app
     * 
     * @param app
     *            the PosTacletApp to be applied
     */
    private void execute(PosTacletApp app) {
        if (app == null) {
            return;
        }
        final KeYMediator mediator = seqView.mediator();
        mediator.applyInteractive(app, mediator.getSelectedGoal());
    }

    /**
     * This popup listener listens to the taclet app selection listener and
     * executes the selected app if necessary
     */
    private class PopupListener implements ActionListener {

        /*
         * (non-Javadoc)
         * 
         * @see java.awt.event.ActionListener#actionPerformed(java.awt.event.ActionEvent)
         */
        public void actionPerformed(ActionEvent e) {
            if (e.getSource() instanceof DefaultTacletMenuItem) {
                final TacletMenuItem item = (TacletMenuItem) e
                        .getSource();
                DragNDropInstantiator.this.execute((PosTacletApp) item
                        .connectedTo());
            }
        }
    }

    /**
     * This interface is impemented by filters selecting certain kinds of
     * taclets depending on their syntactic structure
     */
    protected interface TacletFilter {

        /**
         * This filter selects all Taclet which have an <tt>assumes</tt>,
         * <tt>find</tt> and at least one <tt>replacewith</tt> part.
         */
        TacletFilter TACLET_WITH_IF_FIND_AND_REPLACEWITH = new TacletWithIfFindAndReplacewith();

        /**
         * This filter selects all Taclet which have an <tt>assumes</tt>,
         * <tt>find</tt> and <em>no</em> <tt>replacewith</tt> part.
         */
        TacletFilter TACLET_WITH_IF_FIND_AND_NO_REPLACEWITH = new TacletWithIfFindAndNoReplacewith();

        /**
         * This filter selects all Taclet which have an <tt>assumes</tt>,
         * <tt>find</tt> and <em>no</em> <tt>replacewith</tt> part.
         */
        TacletFilter TACLET_WITH_NO_IF_FIND_AND_ADDRULE = new TacletWithNoIfFindAndAddrule();
          
        /**
         * This filter selects all Taclets which have no <tt>assumes</tt>,
         * sequent but a <tt>find</tt>part.
         */
        TacletFilter TACLET_WITH_NO_IF = new TacletWithNoIf();

        /**
         * checks if the taclet satisfies certain syntactic criterias
         * 
         * @param taclet
         *            the Taclet to be tested
         * @return true if filter condition is fulfilled
         */
        boolean satisfiesFilterCondition(Taclet taclet);

      
        /**
         * This filter selects all Taclet which have an <tt>assumes</tt>,
         * <tt>find</tt> and at least one <tt>replacewith</tt> part.
         */
        class TacletWithIfFindAndReplacewith implements TacletFilter {

            private TacletWithIfFindAndReplacewith() {
            }

            /**
             * tests if the given taclet consists of an <tt>assumes</tt>,
             * <tt>find</tt> and <tt>replacewith</tt> part and returns true
             * if the test is positive
             */
            public boolean satisfiesFilterCondition(Taclet taclet) {
                return taclet.ifSequent() != null
                        && !taclet.ifSequent().isEmpty()
                        && taclet instanceof FindTaclet
                        && taclet.hasReplaceWith();
            }
        }

        /**
         * This filter selects all Taclet which have an <tt>assumes</tt>,
         * <tt>find</tt> and <em>no</em> <tt>replacewith</tt> part.
         */
        class TacletWithIfFindAndNoReplacewith implements TacletFilter {

            private TacletWithIfFindAndNoReplacewith() {
            }

            /**
             * tests if the given taclet consists of an <tt>assumes</tt>,
             * <tt>find</tt> and <em>no</em> <tt>replacewith</tt> part and
             * returns true if the test is positive
             */
            public boolean satisfiesFilterCondition(Taclet taclet) {
                return taclet.ifSequent() != null
                        && !taclet.ifSequent().isEmpty()
                        && taclet instanceof FindTaclet
                        && !taclet.hasReplaceWith();
            }
        }

        /**
         * This filter selects all Taclet which have no <tt>assumes</tt>, but a
         * <tt>find</tt> and at least one <tt>addrule</tt> section.
         */
        class TacletWithNoIfFindAndAddrule implements TacletFilter {

            private TacletWithNoIfFindAndAddrule() {
            }

            /**
             * tests if the goal templates contain at least one addrule section
             * 
             * @param goalDescriptions
             *            the ListOfTacletGoalTemplate to be looked through
             * @return true if an addrule section has been found
             */
            private boolean goalTemplatesContainAddrules(
                    ListOfTacletGoalTemplate goalDescriptions) {
                final IteratorOfTacletGoalTemplate it = goalDescriptions
                        .iterator();
                while (it.hasNext()) {
                    final TacletGoalTemplate tgt = it.next();
                    if (tgt.rules().size() >= 1) {
                        return true;
                    }
                }

                return false;
            }

            /**
             * tests if the given taclet consists of an <tt>assume</tt>,
             * <tt>find</tt> and <em>no</em> <tt>replacewith</tt> part and
             * returns true if the test is positive
             */
            public boolean satisfiesFilterCondition(Taclet taclet) {
                // TODO: the null checks should be unneccessary
                return (taclet.ifSequent() == null || taclet.ifSequent().isEmpty())
                        && taclet instanceof FindTaclet
                        && goalTemplatesContainAddrules(taclet.goalTemplates());
            }
        }
            
            
        /**
         * This filter selects all Taclet which have no <tt>assume</tt>, but a
         * <tt>find</tt>.
         */
        class TacletWithNoIf implements TacletFilter {
            
            private TacletWithNoIf() {
            }
                       
            /**
             * checks if the taclet has a find part and no assumes sequent 
             */
            public boolean satisfiesFilterCondition(Taclet taclet) {
                // TODO: the null checks should be unneccessary
                final Sequent ifSequent = taclet.ifSequent();             
                return ((ifSequent == null || ifSequent.isEmpty()) && 
                        taclet instanceof FindTaclet);
                
            }
            
        }
        
    }
}

