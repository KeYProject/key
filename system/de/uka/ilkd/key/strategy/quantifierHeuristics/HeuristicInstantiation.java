//This file is part of KeY - Integrated Deductive Software Design
//Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                      Universitaet Koblenz-Landau, Germany
//                      Chalmers University of Technology, Sweden
//
//The KeY system is protected by the GNU General Public License. 
//See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.strategy.quantifierHeuristics;

import de.uka.ilkd.key.logic.IteratorOfTerm;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.CastFunctionSymbol;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.sort.AbstractSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.termgenerator.TermGenerator;


public class HeuristicInstantiation implements TermGenerator {
	
    public final static TermGenerator INSTANCE = new HeuristicInstantiation ();
    
    private final TermBuilder tb = TermBuilder.DF;
    
    private HeuristicInstantiation() {}
    
    public IteratorOfTerm generate(RuleApp app,
                                   PosInOccurrence pos,
                                   Goal goal) {
        assert pos != null : "Feature is only applicable to rules with find";

        final Term qf = pos.constrainedFormula ().formula ();
        final Instantiation ia = Instantiation.create ( qf, goal.sequent(), 
                goal.proof().getServices() );
        final QuantifiableVariable var =
            qf.varsBoundHere ( 0 ).lastQuantifiableVariable ();
        return new Iterator ( ia.getSubstitution ().iterator (), var );
    }


    private class Iterator implements IteratorOfTerm {
        private final IteratorOfTerm       instances;

        private final QuantifiableVariable quantifiedVar;

        private final Sort                 quantifiedVarSort;
        private final CastFunctionSymbol   quantifiedVarSortCast;

        private Term                       nextInst = null;

        private Iterator(IteratorOfTerm it, QuantifiableVariable var) {
            this.instances = it;
            this.quantifiedVar = var;
            quantifiedVarSort = quantifiedVar.sort ();
            quantifiedVarSortCast = ( (AbstractSort)quantifiedVarSort ).getCastSymbol ();
            findNextInst ();
        }

        private void findNextInst() {
            while ( nextInst == null && instances.hasNext () ) {
                nextInst = instances.next ();
                if ( !nextInst.sort ().extendsTrans ( quantifiedVarSort ) ) {
                    if ( !quantifiedVarSort.extendsTrans ( nextInst.sort () ) ) {
                        nextInst = null;
                        continue;
                    }
                    nextInst = tb.func ( quantifiedVarSortCast, nextInst );
                }
            }
        }

        public boolean hasNext() {
            return nextInst != null;
        }

        public Term next() {
            final Term res = nextInst;
            nextInst = null;
            findNextInst ();
            return res;
        }
        
        public void remove() {
            throw new UnsupportedOperationException();
        }
    }

}
