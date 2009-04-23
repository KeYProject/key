// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//


package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.logic.ListOfTerm;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.strategy.LongRuleAppCost;
import de.uka.ilkd.key.strategy.TopRuleAppCost;
import de.uka.ilkd.key.strategy.termProjection.ProjectionToTerm;
import de.uka.ilkd.key.strategy.termfeature.*;


/**
 * Feature that returns zero iff each monomial of one polynomial is smaller than
 * all monomials of a second polynomial
 */
public class MonomialsSmallerThanFeature extends AbstractMonomialSmallerThanFeature {

    private final TermFeature  hasCoeff;

    private final ProjectionToTerm left, right;
    private final Function Z, mul, add;


    private MonomialsSmallerThanFeature(ProjectionToTerm left, ProjectionToTerm right, 
                                        IntegerLDT numbers) {
        super ( numbers );
        this.left = left;
        this.right = right;
        this.add = numbers.getAdd();
        this.mul = numbers.getMul ();
        this.Z = numbers.getNumberSymbol ();
        
        hasCoeff = createHasCoeffTermFeature ( numbers );
    }
    
    static TermFeature createHasCoeffTermFeature(final IntegerLDT numbers) {
        return
            BinarySumTermFeature.createSum (
                  OperatorTF.create ( numbers.getMul() ),
                  SubTermFeature.create ( new TermFeature[] {
                        ConstTermFeature.createConst ( LongRuleAppCost.ZERO_COST ),
                        OperatorTF.create ( numbers.getNumberSymbol()) } ) );
    }

    public static Feature create(ProjectionToTerm left, ProjectionToTerm right, 
                                 IntegerLDT numbers) {
        return new MonomialsSmallerThanFeature ( left, right, numbers );
    }
    
    protected boolean filter(TacletApp app, PosInOccurrence pos, Goal goal) {
        final MonomialCollector m1 = new MonomialCollector ();
        m1.collect ( left.toTerm ( app, pos, goal ) );
        final MonomialCollector m2 = new MonomialCollector ();
        m2.collect ( right.toTerm ( app, pos, goal ) );

        setCurrentGoal ( goal );
        
        final boolean res = lessThan ( m1.getResult(), m2.getResult() );
        
        setCurrentGoal ( null );
        
        return res;
    }

    /**
     * this overwrites the method of <code>SmallerThanFeature</code>
     */
    protected boolean lessThan(Term t1, Term t2) {

        // here, the ordering is graded concerning multiplication on integers
        final int t1Deg = degree ( t1 );
        final int t2Deg = degree ( t2 );
        if ( t1Deg < t2Deg ) return true;
        if ( t1Deg > t2Deg ) return false;

        if ( t1Deg == 0 ) {
            // check whether the symbol was introduced as part of a basis
            // transformation; such symbols are smaller than other symbols (and
            // the smaller the later they were introduced)
            
            final int v =
                introductionTime ( t2.op () ) - introductionTime ( t1.op () );
            if ( v < 0 ) return true;
            if ( v > 0 ) return false;
        } else {
            final ListOfTerm atoms1 = collectAtoms ( t1 );
            final ListOfTerm atoms2 = collectAtoms ( t2 );

            if ( atoms1.size () < atoms2.size () ) return false;
            if ( atoms1.size () > atoms2.size () ) return true;
            
            final int v = compareLexNewSyms ( atoms1, atoms2 );
            if ( v < 0 ) return true;
            if ( v > 0 ) return false;
        }
        
        return super.lessThan ( t1, t2 );
    }

    private int compareLexNewSyms(ListOfTerm atoms1, ListOfTerm atoms2) {
        while ( !atoms1.isEmpty() ) {
            final Term t1 = atoms1.head ();
            final Term t2 = atoms2.head ();
            atoms1 = atoms1.tail ();
            atoms2 = atoms2.tail ();
            
            final int c = introductionTime ( t2.op () )
                          - introductionTime ( t1.op () );
            if ( c != 0 ) return c;
        }
        
        return 0;
    }
    
    
    
    /**
     * @return the degree of a monomial (number of terms that are connected
     *         multiplicatively) -1. To ensure that also cases like
     *         <tt>f(a*b)=a*b</tt> are handled properly, we simply count the
     *         total number of multiplication operators in the term.
     */
    private int degree(Term t) {
        int res = 0;
        
        if ( t.op () == mul
             && t.sub ( 0 ).op () != Z && t.sub ( 1 ).op () != Z )
            ++res;

        for ( int i = 0; i != t.arity (); ++i )
            res += degree ( t.sub ( i ) );

        return res;
    }

    private class MonomialCollector extends Collector {
        protected void collect(Term te) {
            if ( te.op () == add ) {
                collect ( te.sub ( 0 ) );
                collect ( te.sub ( 1 ) );
            } else if ( te.op() == Z ) {
              // nothing  
            } else {
                addTerm ( stripOffLiteral ( te ) );
            }
        }

        private Term stripOffLiteral(Term te) {
            if ( ! ( hasCoeff.compute ( te ) instanceof TopRuleAppCost ) )
                // we leave out literals/coefficients on the right, because we
                // do not want to compare these literals
                return te.sub ( 0 );
            return te;
        }
    }
}
