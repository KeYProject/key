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

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Op;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.strategy.termfeature.BinaryTermFeature;
import de.uka.ilkd.key.strategy.termfeature.TermFeature;

public class EliminableQuantifierTF extends BinaryTermFeature {

    public static final TermFeature INSTANCE = new EliminableQuantifierTF ();
    
    private final QuanEliminationAnalyser quanAnalyser =
        new QuanEliminationAnalyser ();
    
    private EliminableQuantifierTF () {}
    
    protected boolean filter(Term term) {
        final Operator op = term.op ();
        assert op == Op.ALL || op == Op.EX;
        
        Term matrix = term;
        do {
            matrix = matrix.sub ( 0 );
        } while ( matrix.op () == term.op () );

        if ( matrix.op () == Op.ALL || matrix.op () == Op.EX ) return false;

        final QuantifiableVariable var =
            term.varsBoundHere ( 0 ).lastQuantifiableVariable ();

        return quanAnalyser.isEliminableVariableAllPaths ( var, matrix, op == Op.EX );
    }
    
}
