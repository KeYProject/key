// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//


package de.uka.ilkd.key.strategy.quantifierHeuristics;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IteratorOfQuantifiableVariable;
import de.uka.ilkd.key.logic.op.Op;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;

public class QuanEliminationAnalyser {
    
    /**
     * 
     * @param definition
     * @return the distance to the quantifier that can be eliminated;
     *         <code>Integer.MAX_VALUE</code> if the subformula is not an
     *         eliminable definition
     */
    public int eliminableDefinition(Term definition, PosInOccurrence envPIO) {
        final PosInOccurrence matrixPIO = walkUpMatrix ( envPIO );
        final Term matrix = matrixPIO.subTerm ();

        if ( matrixPIO.isTopLevel () ) return Integer.MAX_VALUE;
        
        PosInOccurrence quantPIO = matrixPIO.up ();
        Term quantTerm = quantPIO.subTerm ();
        final boolean ex;
        if ( quantTerm.op () == Op.EX ) {
            ex = true;
        } else if ( quantTerm.op () == Op.ALL ) {
            ex = false;
        } else {
            return Integer.MAX_VALUE;
        }
        
        if ( !isDefinitionCandidate ( definition, envPIO.subTerm (), ex ) )
            return Integer.MAX_VALUE;

        int distance = 0;        
        while ( true ) {
            final QuantifiableVariable var =
                quantTerm.varsBoundHere ( 0 ).lastQuantifiableVariable ();

            if ( isDefinition ( definition, var, ex )
                 && isEliminableVariableSomePaths ( var, matrix, ex ) )
                return distance;

            if ( quantPIO.isTopLevel () ) return Integer.MAX_VALUE;
            quantPIO = quantPIO.up ();
            quantTerm = quantPIO.subTerm ();
            
            if ( quantTerm.op () != ( ex ? Op.EX : Op.ALL ) )
                return Integer.MAX_VALUE;
            
            ++distance;
        }
    }

    private boolean isDefinitionCandidate(Term t, Term env, boolean ex) {
        if ( !hasDefinitionShape ( t, ex ) ) return false;
        return !ex || !isBelowOr ( t, env );
    }

    private boolean isBelowOr(Term t, Term env) {
        final Operator envOp = env.op ();
        if ( envOp == Op.OR && ( env.sub ( 0 ) == t || env.sub ( 1 ) == t ) )
            return true;
        if ( envOp == Op.OR || envOp == Op.AND )
            return isBelowOr ( t, env.sub ( 0 ) )
                   || isBelowOr ( t, env.sub ( 1 ) );
        return false;
    }
    
    private boolean hasDefinitionShape(Term t, boolean ex) {
        final IteratorOfQuantifiableVariable it = t.freeVars ().iterator ();
        while ( it.hasNext () ) {
            if ( isDefinition ( t, it.next (), ex ) ) return true;
        }
        return false;
    }
    
    private PosInOccurrence walkUpMatrix(PosInOccurrence pio) {
        while ( !pio.isTopLevel () ) {
            final PosInOccurrence parent = pio.up ();
            final Operator parentOp = parent.subTerm ().op ();
            if ( parentOp != Op.AND && parentOp != Op.OR ) return pio;
            pio = parent;
        }
        return pio;
    }

    /**
     * The variable <code>var</code> is either eliminable or does not occur on
     * all conjunctive/disjunctive paths through <code>matrix</code>
     * (depending on whether <code>ex</code> is true/false)
     */
    public boolean isEliminableVariableSomePaths(QuantifiableVariable var,
                                                 Term matrix,
                                                 boolean ex) {
        if ( !matrix.freeVars ().contains ( var ) ) return true;
        
        final Operator op = matrix.op ();

        if ( op == ( ex ? Op.OR : Op.AND ) ) {
            return isEliminableVariableSomePaths ( var, matrix.sub ( 0 ), ex )
                   && isEliminableVariableSomePaths ( var, matrix.sub ( 1 ), ex );
        } else if ( op == ( ex ? Op.AND : Op.OR ) ) {
            return
            isEliminableVariableAllPaths ( var, matrix.sub ( 0 ), ex )
             || isEliminableVariableAllPaths ( var, matrix.sub ( 1 ), ex )
             || ( isEliminableVariableSomePaths ( var, matrix.sub ( 0 ), ex )
                  && isEliminableVariableSomePaths ( var, matrix.sub ( 1 ), ex ) );
        }

        if ( ex )
            return isDefiningEquationEx ( matrix, var );
        else
            return isDefiningEquationAll ( matrix, var );
    }
    
    /**
     * The variable <code>var</code> is eliminable on all
     * conjunctive/disjunctive paths through <code>matrix</code> (depending on
     * whether <code>ex</code> is true/false)
     */
    public boolean isEliminableVariableAllPaths(QuantifiableVariable var,
                                                Term matrix,
                                                boolean ex) {
        final Operator op = matrix.op ();

        if ( op == ( ex ? Op.OR : Op.AND ) ) {
            return isEliminableVariableAllPaths ( var, matrix.sub ( 0 ), ex )
                   && isEliminableVariableAllPaths ( var, matrix.sub ( 1 ), ex );
        } else if ( op == ( ex ? Op.AND : Op.OR ) ) {
            return isEliminableVariableAllPaths ( var, matrix.sub ( 0 ), ex )
                   || isEliminableVariableAllPaths ( var, matrix.sub ( 1 ), ex );
        }

        if ( ex )
            return isDefiningEquationEx ( matrix, var );
        else
            return isDefiningEquationAll ( matrix, var );
    }
    
    private boolean isDefinition(Term t, QuantifiableVariable var, boolean ex) {
        if ( ex )
            return isDefinitionEx ( t, var );
        else
            return isDefiningEquationAll ( t, var );
    }
    
    private boolean isDefinitionEx(Term t, QuantifiableVariable var) {
        if ( t.op () == Op.OR ) {
            return isDefinitionEx ( t.sub ( 0 ), var )
                   && isDefinitionEx ( t.sub ( 1 ), var );
        }
        return isDefiningEquationEx ( t, var );
    }
    
    private boolean isDefiningEquationAll(Term t, QuantifiableVariable var) {
        if ( t.op () != Op.NOT ) return false;
        return isDefiningEquation ( t.sub ( 0 ), var );
    }

    private boolean isDefiningEquationEx(Term t, QuantifiableVariable var) {
        return isDefiningEquation ( t, var );
    }

    private boolean isDefiningEquation(Term t, QuantifiableVariable var) {
        if ( t.op () != Op.EQUALS ) return false;
        final Term left = t.sub ( 0 );
        final Term right = t.sub ( 1 );
        final Operator leftOp = left.op ();
        final Operator rightOp = right.op ();
        return leftOp == var && !right.freeVars ().contains ( var )
               || rightOp == var && !left.freeVars ().contains ( var );
    }
    
}
