// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.strategy.feature;

import java.util.Iterator;

import org.key_project.util.LRUCache;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableMapEntry;

import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.SkolemTermSV;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.RuleSet;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.inst.InstantiationEntry;

public abstract class AbstractMonomialSmallerThanFeature
                                         extends SmallerThanFeature {
    
    private static final Name newSymRuleSetName = new Name ( "polySimp_newSmallSym" );
    private final Function add, mul, Z;


    protected AbstractMonomialSmallerThanFeature(IntegerLDT numbers) {
        this.add = numbers.getAdd();
        this.mul = numbers.getMul();
        this.Z = numbers.getNumberSymbol ();
    }

    protected int introductionTime(Operator op, Goal goal) {
        if ( op == add || op == mul || op == Z ) return -1;

        final LRUCache<Operator, Integer> introductionTimeCache = 
                goal.proof().getServices().getCaches().getIntroductionTimeCache();
        Integer res;
        
        synchronized (introductionTimeCache) {
            res = introductionTimeCache.get ( op );
        }
        
        if ( res == null ) {
            res = Integer.valueOf ( introductionTimeHelp ( op, goal ) );
            synchronized (introductionTimeCache) {
                introductionTimeCache.put ( op, res );
            }
        }
        
        return res.intValue ();
    }

    private int introductionTimeHelp(Operator op, Goal goal) {
        ImmutableList<RuleApp> appliedRules = goal.appliedRuleApps ();
        while ( !appliedRules.isEmpty () ) {
            final RuleApp app = appliedRules.head ();
            appliedRules = appliedRules.tail ();
            
            if ( app instanceof TacletApp ) {
                final TacletApp tapp = (TacletApp)app;
                if ( !inNewSmallSymRuleSet ( tapp ) ) continue;
                
                if ( introducesSkolemSymbol ( tapp, op ) )
                    return appliedRules.size ();
            }
        }
        
        return -1;
    }

    private boolean introducesSkolemSymbol(TacletApp tapp, Operator op) {
        final Iterator<ImmutableMapEntry<SchemaVariable,InstantiationEntry<?>>> it =
            tapp.instantiations().pairIterator();
        while ( it.hasNext () ) {
            final ImmutableMapEntry<SchemaVariable,InstantiationEntry<?>> entry = it.next ();
            if ( !(entry.key () instanceof SkolemTermSV) ) continue;
            if ( op == ( (Term)entry.value ().getInstantiation () ).op () )
                return true;
        }
        return false;
    }

    private boolean inNewSmallSymRuleSet(TacletApp tapp) {
        ImmutableList<RuleSet> ruleSets = tapp.taclet ().getRuleSets ();
        while ( !ruleSets.isEmpty () ) {
            final RuleSet rs = ruleSets.head ();
            ruleSets = ruleSets.tail ();
            if ( rs.name ().equals ( newSymRuleSetName ) ) return true;
        }
        return false;
    }

    protected ImmutableList<Term> collectAtoms(Term t) {
        final AtomCollector m = new AtomCollector ();
        m.collect ( t );
        return m.getResult ();
    }
    
    private class AtomCollector extends Collector {
        protected void collect(Term te) {
            if ( te.op () == mul ) {
                collect ( te.sub ( 0 ) );
                collect ( te.sub ( 1 ) );
            } else {
                addTerm ( te );
            }
        }
    }
}