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

package de.uka.ilkd.key.strategy.feature.findprefix;

import de.uka.ilkd.key.logic.PIOPathIterator;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.op.IfThenElse;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.Operator;

/**
 * Checks, whether the position in occurrence has antecedent/succedent polarity.
 * 
 * @author christoph
 */
class AntecSuccPrefixChecker implements Checker {

    private static enum Polarity {

        ANTECEDENT, SUCCEDENT

    }

    // checks, whether the position in occurrence has antecedent polarity
    public static final AntecSuccPrefixChecker ANTE_POLARITY_CHECKER =
            new AntecSuccPrefixChecker(Polarity.ANTECEDENT);

    // checks, whether the position in occurrence has succedent polarity
    public static final AntecSuccPrefixChecker SUCC_POLARITY_CHECKER =
            new AntecSuccPrefixChecker(Polarity.SUCCEDENT);

    private AntecSuccPrefixChecker.Polarity polarity;


    private AntecSuccPrefixChecker(
            AntecSuccPrefixChecker.Polarity polarity) {
        this.polarity = polarity;
    }
    
    private int checkOperator(Operator op, int child, int pol) {        
        // compute polarity
        // toggle polarity if find term is subterm of
        if ((op == Junctor.NOT) ||                                          //   not
                (op == Junctor.IMP && child == 0)) {                    //   left hand side of implication
            pol = pol * -1;
            // do not change polarity if find term is subterm of
        } else if ((op == Junctor.AND) ||                                   //   and
                (op == Junctor.OR) ||                                    //   or
                (op == Junctor.IMP && child != 0) ||             //   right hand side of implication
                (op == IfThenElse.IF_THEN_ELSE &&  child!= 0)) { //   then or else part of if-then-else
            // do nothing
        } else {                                                            // find term has no polarity in any other case
            pol = 0;
        }
        return pol;
    }
    
    @Override
    public boolean check(PosInOccurrence pio) {
        int pol = pio.isInAntec() ? -1 : 1;
        if (pio.posInTerm() != null) {
            final PIOPathIterator it = pio.iterator();
            while (pol != 0 && it.next() != -1) {
                pol = checkOperator(pio.subTerm().op(), it.getChild(), pol);
                if (pol == 0) { 
                    break;
                }
            }
        }         
        
        if ((polarity == Polarity.ANTECEDENT && pol != -1) ||
            (polarity == Polarity.SUCCEDENT && pol != 1)) {
            return false;
        } else {
            return true;
        }
    }
}