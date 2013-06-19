/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package de.uka.ilkd.key.strategy.feature.findprefix;

import de.uka.ilkd.key.logic.PIOPathIterator;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.op.IfThenElse;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.Operator;


/**
 *
 * @author christoph
 */
class AntecSuccPrefixChecker implements Checker {

    private static enum Polarity {

        ANTECEDENT, SUCCEDENT

    };

    public static final AntecSuccPrefixChecker ANTE_POLARITY_CHECKER =
            new AntecSuccPrefixChecker(Polarity.ANTECEDENT);

    public static final AntecSuccPrefixChecker SUCC_POLARITY_CHECKER =
            new AntecSuccPrefixChecker(Polarity.SUCCEDENT);

    private AntecSuccPrefixChecker.Polarity polarity;

    private int pol;


    private AntecSuccPrefixChecker(
            AntecSuccPrefixChecker.Polarity polarity) {
        this.polarity = polarity;
    }


    @Override
    public void initPrefixCheck(PosInOccurrence p_pos) {
        pol = p_pos.isInAntec() ? -1 : 1;  // init polarity
    }


    @Override
    public void checkOperator(Operator op,
                              PIOPathIterator it) {
        // compute polarity
        // toggle polarity if find term is subterm of
        if ((op == Junctor.NOT) ||                                          //   not
            (op == Junctor.IMP && it.getChild() == 0)) {                    //   left hand side of implication
            pol = pol * -1;
            // do not change polarity if find term is subterm of
        } else if ((op == Junctor.AND) ||                                   //   and
                   (op == Junctor.OR) ||                                    //   or
                   (op == Junctor.IMP && it.getChild() != 0) ||             //   right hand side of implication
                   (op == IfThenElse.IF_THEN_ELSE && it.getChild() != 0)) { //   then or else part of if-then-else
            // do nothing
        } else {                                                            // find term has no polarity in any other case
            pol = 0;
        }
    }


    @Override
    public boolean getResult() {
        if ((polarity == Polarity.ANTECEDENT && pol != -1) ||
            (polarity == Polarity.SUCCEDENT && pol != 1)) {
            return false;
        } else {
            return true;
        }
    }
}
