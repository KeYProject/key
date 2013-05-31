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


package de.uka.ilkd.key.strategy.feature;

import java.util.Iterator;

import de.uka.ilkd.key.collection.ImmutableMap;
import de.uka.ilkd.key.collection.ImmutableMapEntry;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.SkolemTermSV;
import de.uka.ilkd.key.logic.op.VariableSV;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.IfFormulaInstantiation;
import de.uka.ilkd.key.rule.PosTacletApp;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.inst.InstantiationEntry;
import de.uka.ilkd.key.rule.inst.SVInstantiations;



public abstract class AbstractNonDuplicateAppFeature extends BinaryTacletAppFeature {

    protected AbstractNonDuplicateAppFeature () {}
    
    /**
     * Compare whether two <code>PosInOccurrence</code>s are equal. This can be
     * done using <code>equals</code> or <code>eqEquals</code> (checking for
     * same or equal formulas), which has to be decided by the subclasses
     */
    protected abstract boolean comparePio(TacletApp newApp,
                                          TacletApp oldApp,
                                          PosInOccurrence newPio,
                                          PosInOccurrence oldPio);

    /**
     * Check whether a semisequent contains a formula. Again, one can either
     * search for the same or an equal formula
     */
    protected abstract boolean semiSequentContains(Semisequent semisequent,
                                                   SequentFormula cfma);


    /**
     * Check whether the old rule application <code>ruleCmp</code> is a
     * duplicate of the new application <code>newApp</code> at position
     * <code>newPio</code>.<code>newPio</code> can be <code>null</code>
     */
    protected boolean sameApplication(RuleApp ruleCmp,
                                      TacletApp newApp,
                                      PosInOccurrence newPio) {
        // compare the rules
        if ( newApp.rule () != ruleCmp.rule () ) {
            return false;
        }

        final TacletApp cmp = (TacletApp)ruleCmp;
	
        // compare the position of application
        if ( newPio != null ) {
            if ( ! ( cmp instanceof PosTacletApp ) ) return false;
            final PosInOccurrence oldPio = ((PosTacletApp)cmp).posInOccurrence ();
            if ( !comparePio ( newApp, cmp, newPio, oldPio ) ) return false;
        }

        
        // compare the if-sequent instantiations
        if ( newApp.ifFormulaInstantiations () == null
                || cmp.ifFormulaInstantiations () == null ) {  
            if ( newApp.ifFormulaInstantiations () != null
                    || cmp.ifFormulaInstantiations () != null ) { 
                return false;
            } 
        } else { 
            final Iterator<IfFormulaInstantiation> it0 =
                newApp.ifFormulaInstantiations ().iterator ();
            final Iterator<IfFormulaInstantiation> it1 =
                cmp.ifFormulaInstantiations ().iterator ();

            while ( it0.hasNext () ) {
                // this test should be improved
                if ( it0.next ().getConstrainedFormula ()
                        != it1.next ().getConstrainedFormula () )
                    return false;
            }
        }
        
        return equalInterestingInsts ( newApp.instantiations (),
                                       cmp.instantiations () );
    }

    private boolean equalInterestingInsts (SVInstantiations inst0, SVInstantiations inst1) {
        if ( !inst0.getUpdateContext ().equals ( inst1.getUpdateContext () ) )
            return false;
        
        final ImmutableMap<SchemaVariable,InstantiationEntry> interesting0 =
            inst0.interesting ();
        final ImmutableMap<SchemaVariable,InstantiationEntry> interesting1 =
            inst1.interesting ();
        return subset ( interesting0, interesting1 )
               && subset ( interesting1, interesting0 );
    }
    
    private boolean subset(ImmutableMap<SchemaVariable,InstantiationEntry> insts0,
                           ImmutableMap<SchemaVariable,InstantiationEntry> insts1) {
        final Iterator<ImmutableMapEntry<SchemaVariable,InstantiationEntry>> it =
            insts0.entryIterator ();

        while ( it.hasNext () ) {
            final ImmutableMapEntry<SchemaVariable,InstantiationEntry> entry0 = it.next ();

            if ( entry0.key () instanceof SkolemTermSV || entry0.key() instanceof VariableSV)
                continue;
                
            final InstantiationEntry instEntry1 = insts1.get ( entry0.key () );
            
            if ( instEntry1 == null
                 || !entry0.value ().getInstantiation ()
                     .equals ( instEntry1.getInstantiation () ) )
                return false;
        }
        
        return true;
    }
    
    /**
     * Search for a duplicate of the application <code>app</code> by walking
     * upwards in the proof tree. Here, we assume that <code>pos</code> is
     * non-null, and as an optimisation we stop as soon as we have reached a
     * point where the formula containing the focus no longer occurs in the
     * sequent
     */
    protected boolean noDuplicateFindTaclet(TacletApp app,
                                            PosInOccurrence pos,
                                            Goal goal) {
        final SequentFormula focusFor = pos.constrainedFormula ();
        final boolean antec = pos.isInAntec ();
    
        Node node = goal.node ();
    
        int i = 0;
        while ( !node.root () ) {
            final Node par = node.parent ();
            
            ++i;
            if ( i > 100 ) {
                i = 0;

                final Sequent pseq = par.sequent ();
                if ( antec ) {
                    if ( !semiSequentContains ( pseq.antecedent (), focusFor ) )
                        return true;
                } else {
                    if ( !semiSequentContains ( pseq.succedent (), focusFor ) )
                        return true;
                }
            }
            
            if ( sameApplication ( par.getAppliedRuleApp (), app, pos ) )
                    return false;
    
            node = par;
        }
    
        return true;
    }

}
