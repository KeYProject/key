// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.rule.ListOfNoPosTacletApp;
import de.uka.ilkd.key.rule.ListOfTacletApp;

/**
 * This class holds <code>TermTacletAppIndex</code>s for all formulas of
 * a semisequent.
 */
public class SemisequentTacletAppIndex {
    private MapFromConstrainedFormulaToTermTacletAppIndex
	termIndices = MapAsListFromConstrainedFormulaToTermTacletAppIndex.EMPTY_MAP;

    private TermTacletAppIndexCacheSet indexCaches;
    
    private final RuleFilter ruleFilter;

    private final Sequent seq;
    private final boolean antec;

    /**
     * Add indices for the given formulas to the map
     * <code>termIndices</code>. Existing entries are replaced with
     * the new indices.
     * Note: destructive, use only when constructing new index
     */
    private void addTermIndices ( ListOfConstrainedFormula cfmas,
                                  Sequent                  s,
                                  Services                 services,
                                  Constraint               userConstraint,
                                  TacletIndex              tacletIndex,
                                  NewRuleListener          listener ) {
        while ( !cfmas.isEmpty() ) {
            final ConstrainedFormula cfma = cfmas.head ();
            cfmas = cfmas.tail ();
            addTermIndex ( cfma, s, services, userConstraint, tacletIndex,
                           listener );
        }
    }

    /**
     * Add an index for the given formula to the map
     * <code>termIndices</code>. An existing entry is replaced with
     * the new one.
     * Note: destructive, use only when constructing new index
     */
    private void addTermIndex ( ConstrainedFormula cfma,
                                Sequent            s,
                                Services           services,
                                Constraint         userConstraint,
                                TacletIndex        tacletIndex,
                                NewRuleListener    listener ) {
        final PosInOccurrence pos =
            new PosInOccurrence ( cfma, PosInTerm.TOP_LEVEL, antec );

        termIndices =
            termIndices.put ( cfma, TermTacletAppIndex.create ( pos,
                                                                services,
                                                                userConstraint,
                                                                tacletIndex,
                                                                listener,
                                                                ruleFilter,
                                                                indexCaches ) );
    }

    /**
     * Update the index for the given formula, which is supposed to be an
     * element of the map <code>termIndices</code>, by adding the taclets that
     * are selected by <code>filter</code>
     * Note: destructive, use only when constructing new index
     */
    private void addTaclets ( RuleFilter         filter, 
                              ConstrainedFormula cfma,
                              Sequent            s,
                              Services           services,
                              Constraint         userConstraint,
                              TacletIndex        tacletIndex,
                              NewRuleListener    listener ) {
        final TermTacletAppIndex oldIndex = termIndices.get ( cfma );
        assert oldIndex != null :
            "Term index that is supposed to be updated " +
            "does not exist";
    
        final PosInOccurrence pos =
            new PosInOccurrence ( cfma, PosInTerm.TOP_LEVEL, antec );

        termIndices = termIndices.put ( cfma,
                                        oldIndex.addTaclets ( filter,
                                                              pos,
                                                              services,
                                                              userConstraint,
                                                              tacletIndex,
                                                              listener ) );
    }

    /**
     * Remove the indices for the given formulas from the map
     * <code>termIndices</code>.
     * Note: destructive, use only when constructing new index
     */
    private void removeTermIndices(ListOfConstrainedFormula cfmas) {
        final IteratorOfConstrainedFormula it = cfmas.iterator ();
        while ( it.hasNext () )
            removeTermIndex ( it.next () );
    }

    /**
     * Remove the index for the given formula from the map
     * <code>termIndices</code>.
     * Note: destructive, use only when constructing new index
     */
    private void removeTermIndex ( ConstrainedFormula cfma ) {
        termIndices = termIndices.remove ( cfma );	
    }

    /**
     * Remove the formulas that are listed as modified by
     * <code>infos</code>
     * @return the old indices in the same order as the list
     * <code>infos</code>
     * Note: destructive, use only when constructing new index
     */
    private ListOfTermTacletAppIndex removeFormulas(ListOfFormulaChangeInfo infos) {

        ListOfTermTacletAppIndex oldIndices = SLListOfTermTacletAppIndex.EMPTY_LIST;

        final IteratorOfFormulaChangeInfo infoIt = infos.iterator ();

        while ( infoIt.hasNext () ) {
            final FormulaChangeInfo info = infoIt.next ();
            final ConstrainedFormula oldFor = info.getOriginalFormula ();
            final ConstrainedFormula newFor = info.getNewFormula ();

            TermTacletAppIndex oldIndex;

            if ( oldFor.constraint ().equals ( newFor.constraint () ) ) {
                oldIndex = termIndices.get ( oldFor );
            } else {
                // modified constraint, thus we have to rebuild the whole term
                // index
                oldIndex = null;
            }
            oldIndices = oldIndices.prepend ( oldIndex );
            termIndices = termIndices.remove ( oldFor );
        }

        return oldIndices.reverse ();
    }

    /**
     * Update the given list of term indices according to the list
     * <code>infos</code> of modification information. Both lists have
     * to be compatible, i.e. same length and same order. The new
     * indices are inserted in the map <code>termIndices</code>.
     * Note: destructive, use only when constructing new index
     */
    private void updateTermIndices ( ListOfTermTacletAppIndex oldIndices,
                                     ListOfFormulaChangeInfo  infos,
                                     Sequent                  newSeq,
                                     Services                 services,
                                     Constraint               userConstraint,
                                     TacletIndex              tacletIndex,
                                     NewRuleListener          listener ) {

	final IteratorOfFormulaChangeInfo infoIt = infos.iterator ();
        final IteratorOfTermTacletAppIndex oldIndexIt = oldIndices.iterator ();

        while ( infoIt.hasNext () ) {
            final FormulaChangeInfo info = infoIt.next ();
            final ConstrainedFormula newFor = info.getNewFormula ();
            final TermTacletAppIndex oldIndex = oldIndexIt.next ();

            if ( oldIndex == null )
                // completely rebuild the term index
                addTermIndex ( newFor, newSeq, services, userConstraint,
                               tacletIndex, listener );
            else {
                final PosInOccurrence oldPos = info.getPositionOfModification ();
                final PosInOccurrence newPos = oldPos.replaceConstrainedFormula ( newFor );
                termIndices = termIndices.put ( newFor,
                                                oldIndex.update ( newPos,
                                                                  services,
                                                                  userConstraint,
                                                                  tacletIndex,
                                                                  listener,
                                                                  indexCaches ) );
            }
        }
    }

    private void updateTermIndices ( ListOfFormulaChangeInfo infos,
                                     Sequent                 newSeq,
                                     Services                services,
                                     Constraint              userConstraint,
                                     TacletIndex             tacletIndex,
                                     NewRuleListener         listener ) {

        // remove original indices
        final ListOfTermTacletAppIndex oldIndices = removeFormulas ( infos );

        updateTermIndices ( oldIndices, infos, newSeq, services,
                            userConstraint, tacletIndex, listener );
    }
    
    /**
     * Create an index object for the semisequent determined by
     * <code>s</code> and <code>antec</code> that contains term
     * indices for each formula.
     * @param antec iff true create an index for the antecedent of
     * <code>s</code>, otherwise for the succedent
     */
    public SemisequentTacletAppIndex ( Sequent         s,
                                       boolean         antec,
                                       Services        services,
                                       Constraint      userConstraint,
                                       TacletIndex     tacletIndex,
                                       NewRuleListener listener,
                                       RuleFilter      ruleFilter,
                                       TermTacletAppIndexCacheSet indexCaches) {
        this.seq = s;
        this.antec = antec;
        this.ruleFilter = ruleFilter;
        this.indexCaches = indexCaches;
        addTermIndices ( ( antec ? s.antecedent () : s.succedent () ).toList (),
                         s, services, userConstraint, tacletIndex, listener );
    }

    private SemisequentTacletAppIndex ( SemisequentTacletAppIndex orig ) {
        this.seq          = orig.seq;
        this.antec        = orig.antec;
        this.ruleFilter   = orig.ruleFilter;
        this.termIndices  = orig.termIndices;
        this.indexCaches  = orig.indexCaches;
    }

    public SemisequentTacletAppIndex copy() {
        return new SemisequentTacletAppIndex ( this );
    }

    /**
     * Get term index for the formula to which position <code>pos</code> points
     */ 
    private TermTacletAppIndex getTermIndex(PosInOccurrence pos) {
        return termIndices.get ( pos.constrainedFormula () );
    }

    /**
     * @return all taclet apps for the given position
     */
    public ListOfNoPosTacletApp getTacletAppAt(PosInOccurrence pos,
                                               RuleFilter filter) {
        return getTermIndex ( pos ).getTacletAppAt ( pos, filter );
    }

    /**
     * @return all taclet apps for or below the given position
     */
    public ListOfTacletApp getTacletAppAtAndBelow(PosInOccurrence pos,
                                                  RuleFilter filter) {
        return getTermIndex ( pos ).getTacletAppAtAndBelow ( pos, filter );
    }

    /** 
     * called if a formula has been replaced
     * @param sci SequentChangeInfo describing the change of the sequent 
     */  
    public SemisequentTacletAppIndex sequentChanged ( SequentChangeInfo sci,
                                                      Services          services,
                                                      Constraint        userConstraint,
                                                      TacletIndex       tacletIndex,
                                                      NewRuleListener   listener) {
        if ( sci.hasChanged ( antec ) ) {
            final SemisequentTacletAppIndex result = copy ();
            result.removeTermIndices ( sci.removedFormulas ( antec ) );
            result.updateTermIndices ( sci.modifiedFormulas ( antec ),
                                       sci.sequent (), services,
                                       userConstraint, tacletIndex, listener );
            result.addTermIndices ( sci.addedFormulas ( antec ),
                                    sci.sequent (), services, userConstraint,
                                    tacletIndex, listener );
            return result;
        }
        
        return this;
    }
    
    
    /**
     * Create an index that additionally contains the taclets that are selected
     * by <code>filter</code>
     * @param filter The taclets that are supposed to be added
     */
    public SemisequentTacletAppIndex addTaclets ( RuleFilter      filter,
                                                  Sequent         s,
                                                  Services        services,
                                                  Constraint      userConstraint,
                                                  TacletIndex     tacletIndex,
                                                  NewRuleListener listener) {
        final SemisequentTacletAppIndex result = copy();
        final IteratorOfConstrainedFormula it = termIndices.keyIterator ();

        while ( it.hasNext () )
            result.addTaclets ( filter, it.next (), s, services,
                                userConstraint, tacletIndex, listener );

        return result;
    }
    
    /**
     * Reports all cached rule apps.
     * Calls ruleAdded on the given NewRuleListener for
     * every cached taclet app.
     */
    public void reportRuleApps ( NewRuleListener l ) {
        final IteratorOfEntryOfConstrainedFormulaAndTermTacletAppIndex it =
            termIndices.entryIterator();
        
        while ( it.hasNext() ) {
            final EntryOfConstrainedFormulaAndTermTacletAppIndex entry = it.next();
            final ConstrainedFormula cfma = entry.key (); 
            final TermTacletAppIndex index = entry.value ();
            final PosInOccurrence pio = 
                new PosInOccurrence ( cfma, PosInTerm.TOP_LEVEL, antec );
            
            index.reportTacletApps( pio, l );
        }
    }
    
    public void setIndexCache(TermTacletAppIndexCacheSet indexCaches) {
        this.indexCaches = indexCaches;
    }
}
