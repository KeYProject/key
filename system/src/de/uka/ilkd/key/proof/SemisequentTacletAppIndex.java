// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 


package de.uka.ilkd.key.proof;

import java.util.Iterator;

import de.uka.ilkd.key.collection.*;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.proof.rulefilter.RuleFilter;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.TacletApp;

/**
 * This class holds <code>TermTacletAppIndex</code>s for all formulas of
 * a semisequent.
 */
public class SemisequentTacletAppIndex {
    private ImmutableMap<SequentFormula,TermTacletAppIndex>
	termIndices = DefaultImmutableMap.<SequentFormula,TermTacletAppIndex>nilMap();

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
    private void addTermIndices ( ImmutableList<SequentFormula> cfmas,
                                  Sequent                  s,
                                  Services                 services,
                                  TacletIndex              tacletIndex,
                                  NewRuleListener          listener ) {
        while ( !cfmas.isEmpty() ) {
            final SequentFormula cfma = cfmas.head ();
            cfmas = cfmas.tail ();
            addTermIndex ( cfma, s, services, tacletIndex, listener );
        }
    }

    /**
     * Add an index for the given formula to the map
     * <code>termIndices</code>. An existing entry is replaced with
     * the new one.
     * Note: destructive, use only when constructing new index
     */
    private void addTermIndex ( SequentFormula cfma,
                                Sequent            s,
                                Services           services,
                                TacletIndex        tacletIndex,
                                NewRuleListener    listener ) {
        final PosInOccurrence pos =
            new PosInOccurrence ( cfma, PosInTerm.getTopLevel(), antec );
        termIndices =
            termIndices.put ( cfma, TermTacletAppIndex.create ( pos,
                                                                services,
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
                              SequentFormula cfma,
                              Sequent            s,
                              Services           services,
                              TacletIndex        tacletIndex,
                              NewRuleListener    listener ) {
        final TermTacletAppIndex oldIndex = termIndices.get ( cfma );
        assert oldIndex != null :
            "Term index that is supposed to be updated " +
            "does not exist";
    
        final PosInOccurrence pos =
            new PosInOccurrence ( cfma, PosInTerm.getTopLevel(), antec );

        termIndices = termIndices.put ( cfma,
                                        oldIndex.addTaclets ( filter,
                                                              pos,
                                                              services,
                                                              tacletIndex,
                                                              listener ) );
    }

    /**
     * Remove the indices for the given formulas from the map
     * <code>termIndices</code>.
     * Note: destructive, use only when constructing new index
     */
    private void removeTermIndices(ImmutableList<SequentFormula> cfmas) {
        for (SequentFormula cfma : cfmas) removeTermIndex(cfma);
    }

    /**
     * Remove the index for the given formula from the map
     * <code>termIndices</code>.
     * Note: destructive, use only when constructing new index
     */
    private void removeTermIndex ( SequentFormula cfma ) {
        termIndices = termIndices.remove ( cfma );	
    }

    /**
     * Remove the formulas that are listed as modified by
     * <code>infos</code>
     * @return the old indices in the same order as the list
     * <code>infos</code>
     * Note: destructive, use only when constructing new index
     */
    private ImmutableList<TermTacletAppIndex> removeFormulas(ImmutableList<FormulaChangeInfo> infos) {

        ImmutableList<TermTacletAppIndex> oldIndices = ImmutableSLList.<TermTacletAppIndex>nil();

        for (FormulaChangeInfo info1 : infos) {
            final FormulaChangeInfo info = info1;
            final SequentFormula oldFor = info.getOriginalFormula();

            oldIndices = oldIndices.prepend(termIndices.get(oldFor));
            termIndices = termIndices.remove(oldFor);
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
    private void updateTermIndices ( ImmutableList<TermTacletAppIndex> oldIndices,
                                     ImmutableList<FormulaChangeInfo>  infos,
                                     Sequent                  newSeq,
                                     Services                 services,
                                     TacletIndex              tacletIndex,
                                     NewRuleListener          listener ) {

	final Iterator<FormulaChangeInfo> infoIt = infos.iterator ();
        final Iterator<TermTacletAppIndex> oldIndexIt = oldIndices.iterator ();

        while ( infoIt.hasNext () ) {
            final FormulaChangeInfo info = infoIt.next ();
            final SequentFormula newFor = info.getNewFormula ();
            final TermTacletAppIndex oldIndex = oldIndexIt.next ();

            if ( oldIndex == null )
                // completely rebuild the term index
                addTermIndex ( newFor, newSeq, services, tacletIndex,
                               listener );
            else {
                final PosInOccurrence oldPos = info.getPositionOfModification ();
                final PosInOccurrence newPos = oldPos.replaceConstrainedFormula ( newFor );
                termIndices = termIndices.put ( newFor,
                                                oldIndex.update ( newPos,
                                                                  services,
                                                                  tacletIndex,
                                                                  listener,
                                                                  indexCaches ) );
            }
        }
    }

    private void updateTermIndices ( ImmutableList<FormulaChangeInfo> infos,
                                     Sequent                 newSeq,
                                     Services                services,
                                     TacletIndex             tacletIndex,
                                     NewRuleListener         listener ) {

        // remove original indices
        final ImmutableList<TermTacletAppIndex> oldIndices = removeFormulas ( infos );

        updateTermIndices ( oldIndices, infos, newSeq, services,
                            tacletIndex, listener );
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
                                       TacletIndex     tacletIndex,
                                       NewRuleListener listener,
                                       RuleFilter      ruleFilter,
                                       TermTacletAppIndexCacheSet indexCaches) {
        this.seq = s;
        this.antec = antec;
        this.ruleFilter = ruleFilter;
        this.indexCaches = indexCaches;
        addTermIndices ( ( antec ? s.antecedent () : s.succedent () ).toList (),
                         s, services, tacletIndex, listener );
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
    public ImmutableList<NoPosTacletApp> getTacletAppAt(PosInOccurrence pos,
                                               RuleFilter filter) {
        return getTermIndex ( pos ).getTacletAppAt ( pos, filter );
    }

    /**
     * @return all taclet apps for or below the given position
     */
    public ImmutableList<TacletApp> getTacletAppAtAndBelow(PosInOccurrence pos,
                                                  RuleFilter filter,
                                                  Services services) {
        return getTermIndex ( pos ).getTacletAppAtAndBelow ( pos, filter, services );
    }

    /** 
     * called if a formula has been replaced
     * @param sci SequentChangeInfo describing the change of the sequent 
     */  
    public SemisequentTacletAppIndex sequentChanged ( SequentChangeInfo sci,
                                                      Services          services,
                                                      TacletIndex       tacletIndex,
                                                      NewRuleListener   listener) {
        if ( sci.hasChanged ( antec ) ) {
            final SemisequentTacletAppIndex result = copy ();
            result.removeTermIndices ( sci.removedFormulas ( antec ) );
            result.updateTermIndices ( sci.modifiedFormulas ( antec ),
                                       sci.sequent (), services,
                                       tacletIndex, listener );
            result.addTermIndices ( sci.addedFormulas ( antec ),
                                    sci.sequent (), services, tacletIndex,
                                    listener );
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
                                                  TacletIndex     tacletIndex,
                                                  NewRuleListener listener) {
        final SemisequentTacletAppIndex result = copy();
        final Iterator<SequentFormula> it = termIndices.keyIterator ();

        while ( it.hasNext () )
            result.addTaclets ( filter, it.next (), s, services,
                                tacletIndex, listener );

        return result;
    }
    
    /**
     * Reports all cached rule apps.
     * Calls ruleAdded on the given NewRuleListener for
     * every cached taclet app.
     */
    public void reportRuleApps ( NewRuleListener l ) {
        final Iterator<ImmutableMapEntry<SequentFormula,TermTacletAppIndex>> it =
            termIndices.entryIterator();
        
        while ( it.hasNext() ) {
            final ImmutableMapEntry<SequentFormula,TermTacletAppIndex> entry = it.next();
            final SequentFormula cfma = entry.key (); 
            final TermTacletAppIndex index = entry.value ();
            final PosInOccurrence pio = 
                new PosInOccurrence ( cfma, PosInTerm.getTopLevel(), antec );
            
            index.reportTacletApps( pio, l );
        }
    }
    
    public void setIndexCache(TermTacletAppIndexCacheSet indexCaches) {
        this.indexCaches = indexCaches;
    }
}
