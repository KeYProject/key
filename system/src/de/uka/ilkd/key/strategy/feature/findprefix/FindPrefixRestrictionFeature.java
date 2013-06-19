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
package de.uka.ilkd.key.strategy.feature.findprefix;

import de.uka.ilkd.key.logic.PIOPathIterator;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.strategy.feature.BinaryTacletAppFeature;


/**
 * Feature for investigating whether some restrictions to the prefix of the
 * find formula apply.
 */
public class FindPrefixRestrictionFeature extends BinaryTacletAppFeature {

    public enum PrefixChecker {

        ANTEC(new AntecChecker()),
        SUCC(new SuccChecker()),
        ANTEC_POLARITY(AntecSuccPrefixChecker.ANTE_POLARITY_CHECKER),
        SUCC_POLARITY(AntecSuccPrefixChecker.SUCC_POLARITY_CHECKER),
        TOP_LEVEL(new TopLevelChecker());
        
        private final Checker checker;


        PrefixChecker(Checker checker) {
            this.checker = checker;
        }

        public void initPrefixCheck(PosInOccurrence p_pos) {
            checker.initPrefixCheck(p_pos);
        }


        public void checkOperator(Operator op,
                                  PIOPathIterator it) {
            checker.checkOperator(op, it);
        }


        public boolean getResult() {
            return checker.getResult();
        }
    };

    public enum PositionModifier {
        ALLOW_UPDATE_AS_PARENT(new RemoveParentUpdateModifier());

        private final Modifier modifier;


        private PositionModifier(Modifier modifier) {
            this.modifier = modifier;
        }

        PosInOccurrence modifyPosistion(PosInOccurrence pos) {
            return modifier.modifyPosistion(pos);
        }
    }

    private final PrefixChecker[] prefixCheckers;
    private final PositionModifier[] positionModifiers;


    public FindPrefixRestrictionFeature(PrefixChecker... prefixCheckers) {
        this(new PositionModifier[0], prefixCheckers);
    }

    public FindPrefixRestrictionFeature(PositionModifier positionModifier,
                                        PrefixChecker... prefixCheckers) {
        this(new PositionModifier[]{positionModifier}, prefixCheckers);
    }

    public FindPrefixRestrictionFeature(PositionModifier[] positionModifiers,
                                        PrefixChecker... prefixCheckers) {
        this.positionModifiers = positionModifiers;
        this.prefixCheckers = prefixCheckers;
    }

    @Override
    protected boolean filter(TacletApp app,
                             PosInOccurrence pos,
                             Goal goal) {
        assert pos != null : "Feature is only applicable to rules with find";
        PosInOccurrence newPos = pos;
        for (PositionModifier positionModifier : positionModifiers) {
            newPos = positionModifier.modifyPosistion(pos);
        }
        return checkPrefix(newPos);
    }


    /**
     * For taclets with
     * <code>getSameUpdatePrefix ()</code>, collect the updates above
     * <code>p_pos</code> and add them to the update context of the
     * instantiations object
     * <code>p_mc</code>.
     * <p/>
     * @return the new instantiations with the additional updates, or
     *         <code>null</code>, if program modalities appear above
     *         <code>p_pos</code>
     */
    public boolean checkPrefix(PosInOccurrence pos) {
        for (PrefixChecker prefixChecker : prefixCheckers) {
            prefixChecker.initPrefixCheck(pos);
        }

        if (pos.posInTerm() != null) {
            PIOPathIterator it = pos.iterator();
            Operator op;

            while (it.next() != -1) {
                final Term t = it.getSubTerm();
                op = t.op();

                for (PrefixChecker prefixChecker : prefixCheckers) {
                    prefixChecker.checkOperator(op, it);
                }

            }
        }

        boolean result = true;
        for (PrefixChecker prefixChecker : prefixCheckers) {
            result &= prefixChecker.getResult();
        }
        return result;
    }
}
