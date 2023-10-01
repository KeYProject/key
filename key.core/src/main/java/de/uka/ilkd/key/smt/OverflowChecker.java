/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.smt;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import de.uka.ilkd.key.smt.lang.*;

public class OverflowChecker {
    private final SMTSort intsort;

    public OverflowChecker(SMTSort intsort) {
        super();
        this.intsort = intsort;
    }

    private int max() {

        int bound = (int) Math.pow(2, intsort.getBitSize());

        return bound / 2 - 1;
    }

    private int min() {

        int bound = (int) Math.pow(2, intsort.getBitSize());
        return -bound / 2;

    }


    private SMTTerm increaseBitsize(SMTTerm t) {
        SMTTerm zero = new SMTTermNumber(0, 1, null);
        SMTTerm one = new SMTTermNumber(1, 1, null);

        SMTTerm zeroInt = new SMTTermNumber(0, intsort.getBitSize(), intsort);
        SMTTerm condition = t.gte(zeroInt);

        SMTTerm trueCase = zero.concat(t);
        SMTTerm falseCase = one.concat(t);


        return SMTTerm.ite(condition, trueCase, falseCase);
    }

    private SMTTerm doubleBitsize(SMTTerm t) {
        // 000000...
        SMTTerm zero = new SMTTermNumber(0, intsort.getBitSize(), null);
        // 111111...
        SMTTerm one = new SMTTermNumber(intsort.getBound() - 1, intsort.getBitSize(), null);

        SMTTerm zeroInt = new SMTTermNumber(0, intsort.getBitSize(), intsort);
        SMTTerm condition = t.gte(zeroInt);

        SMTTerm trueCase = zero.concat(t);
        SMTTerm falseCase = one.concat(t);

        return SMTTerm.ite(condition, trueCase, falseCase);
    }

    private SMTTerm createGuardForAdd(SMTTermMultOp t) {

        List<SMTTerm> subs = new LinkedList<>();
        for (SMTTerm sub : t.getSubs()) {
            subs.add(increaseBitsize(sub));
        }
        SMTTerm increasedTerm = new SMTTermMultOp(t.getOperator(), subs);

        long newbound = intsort.getBound() * 2;
        long newMaxInt = max();
        long newMinInt = newbound + min();

        SMTTermNumber max = new SMTTermNumber(newMaxInt, intsort.getBitSize() + 1, null);
        SMTTermNumber min = new SMTTermNumber(newMinInt, intsort.getBitSize() + 1, null);

        SMTTerm assertLEMax = increasedTerm.lte(max);
        SMTTerm assertGEMin = increasedTerm.gte(min);

        return assertLEMax.and(assertGEMin);
    }

    private SMTTerm createGuardForMul(SMTTermMultOp t) {
        List<SMTTerm> subs = new LinkedList<>();
        for (SMTTerm sub : t.getSubs()) {
            subs.add(doubleBitsize(sub));
        }
        SMTTerm increasedTerm = new SMTTermMultOp(t.getOperator(), subs);

        long newbound = intsort.getBound() * intsort.getBound();
        long newMaxInt = max();
        long newMinInt = newbound + min();

        SMTTermNumber max = new SMTTermNumber(newMaxInt, intsort.getBitSize() * 2, null);
        SMTTermNumber min = new SMTTermNumber(newMinInt, intsort.getBitSize() * 2, null);

        SMTTerm assertLEMax = increasedTerm.lte(max);
        SMTTerm assertGEMin = increasedTerm.gte(min);

        return assertLEMax.and(assertGEMin);

    }

    private void getSubTerms(SMTTerm t, Set<SMTTerm> result) {

        if (t instanceof SMTTermMultOp tm) {

            if (isArithmeticOperator(tm.getOperator())) {

                result.add(tm);

                for (SMTTerm sub : tm.getSubs()) {
                    getSubTerms(sub, result);
                }


            }


        }

    }

    private SMTTerm createGuard(Set<SMTTerm> terms) {

        List<SMTTerm> args = createGuards(terms);
        return SMTTerm.and(args);
    }

    /**
     * Creates guards for the given terms
     *
     * @param terms - the terms that must be guarded against integer overflows
     * @return a list of generated guards
     */
    public List<SMTTerm> createGuards(Set<SMTTerm> terms) {
        List<SMTTerm> args = new LinkedList<>();

        for (SMTTerm t : terms) {

            if (t instanceof SMTTermMultOp tm) {
                SMTTerm guard = null;
                // create guard for addition
                if (isAddOp(tm.getOperator())) {
                    guard = createGuardForAdd(tm);

                }
                // create guard for multiplication
                else if (isMulOp(tm.getOperator())) {
                    guard = createGuardForMul(tm);
                }
                if (guard != null) {
                    args.add(guard);
                }

            }


        }
        return args;
    }

    private boolean isArithmeticOperator(SMTTermMultOp.Op op) {
        return op.equals(SMTTermMultOp.Op.BVSDIV) || op.equals(SMTTermMultOp.Op.BVSREM)
                || op.equals(SMTTermMultOp.Op.MUL) || op.equals(SMTTermMultOp.Op.PLUS)
                || op.equals(SMTTermMultOp.Op.MINUS) || op.equals(SMTTermMultOp.Op.BVSMOD);
    }


    private boolean isAddOp(SMTTermMultOp.Op op) {
        return op.equals(SMTTermMultOp.Op.PLUS) || op.equals(SMTTermMultOp.Op.MINUS);
    }

    private boolean isMulOp(SMTTermMultOp.Op op) {
        return op.equals(SMTTermMultOp.Op.MUL);
    }

    private boolean isComparisonOp(SMTTermMultOp.Op op) {
        return op.equals(SMTTermMultOp.Op.BVSGE) || op.equals(SMTTermMultOp.Op.BVSGT)
                || op.equals(SMTTermMultOp.Op.BVSLE) || op.equals(SMTTermMultOp.Op.BVSLT)
                || op.equals(SMTTermMultOp.Op.EQUALS);
    }

    /**
     * Adds a guard for the given term if that term may overflow.
     */
    public SMTTerm addGuardIfNecessary(SMTTerm t) {
        Set<SMTTermVariable> vars = new HashSet<>();
        return addGuardIfNecessary(t, vars);
    }

    /**
     * Constructs a guarded term, if overflows are possible, otherwise returns the original term.
     */
    private SMTTerm addGuardIfNecessary(SMTTerm t, Set<SMTTermVariable> quantifiedVars) {


        if (t instanceof SMTTermMultOp tm) {
            // we look for comparison terms like a < b
            if (isComparisonOp(tm.getOperator())) {
                SMTTerm left = tm.getSubs().get(0);
                SMTTerm right = tm.getSubs().get(1);

                Set<SMTTerm> leftSubs = new HashSet<>();
                Set<SMTTerm> rightSubs = new HashSet<>();

                getSubTerms(left, leftSubs); // sub terms of the left side
                getSubTerms(right, rightSubs); // sub terms of the right side

                // classify sub terms in universally and existentially quantified subs
                Set<SMTTerm> universalSubs = new HashSet<>();
                Set<SMTTerm> existentialSubs = new HashSet<>();

                classifySubs(quantifiedVars, leftSubs, universalSubs, existentialSubs);
                classifySubs(quantifiedVars, rightSubs, universalSubs, existentialSubs);
                // create universal and existential guards
                SMTTerm universalGuard = createGuard(universalSubs);
                SMTTerm existentialGuard = createGuard(existentialSubs);

                // return the guarded term
                return existentialGuard.and(universalGuard.implies(t));
            }
        }
        return t;
    }

    /**
     * Recursively adds overflow guards for non ground terms if necessary.
     */
    public void processTerm(SMTTerm t) {
        Set<SMTTermVariable> uvars = new HashSet<>();
        Set<SMTTermVariable> evars = new HashSet<>();
        processTerm(t, uvars, evars);
    }


    private void processTerm(SMTTerm t, Set<SMTTermVariable> universalVars,
            Set<SMTTermVariable> existentialVars) {

        if (t instanceof SMTTermMultOp tm) {
            List<SMTTerm> subs = tm.getSubs();
            for (SMTTerm sub : subs) {
                processTerm(sub, universalVars, existentialVars);
            }


        } else if (t instanceof SMTTermCall tc) {
            List<SMTTerm> subs = tc.getArgs();

            for (SMTTerm sub : subs) {
                processTerm(sub, universalVars, existentialVars);
            }

        } else if (t instanceof SMTTermQuant tq) {
            SMTTerm sub = tq.getSub();
            if (tq.getQuant().equals(SMTTermQuant.Quant.FORALL)) {
                universalVars.addAll(tq.getBindVars());
            } else {
                existentialVars.addAll(tq.getBindVars());
            }


            Set<SMTTerm> terms = new HashSet<>();

            searchArithTerms(terms, tq.getSub(), universalVars, existentialVars, tq.getBindVars());


            SMTTerm guard = createGuard(terms);
            processTerm(sub, universalVars, existentialVars);
            if (tq.getQuant().equals(SMTTermQuant.Quant.FORALL)) {
                tq.setSub(guard.implies(tq.getSub()));
                universalVars.removeAll(tq.getBindVars());
            } else {
                tq.setSub(guard.and(tq.getSub()));
                existentialVars.removeAll(tq.getBindVars());
            }


        } else if (t instanceof SMTTermUnaryOp tu) {
            SMTTerm sub = tu.getSub();
            SMTTerm guarded = addGuardIfNecessary(sub, universalVars);
            if (!sub.equals(guarded)) {
                tu.setSub(guarded);
            }
            processTerm(tu.getSub(), universalVars, existentialVars);
        } else if (t instanceof SMTTermITE ite) {
            SMTTerm cond = ite.getCondition();
            SMTTerm trueCase = ite.getTrueCase();
            SMTTerm falseCase = ite.getFalseCase();

            processTerm(ite.getCondition(), universalVars, existentialVars);
            processTerm(ite.getTrueCase(), universalVars, existentialVars);
            processTerm(ite.getFalseCase(), universalVars, existentialVars);

            SMTTerm gcond = addGuardIfNecessary(cond, universalVars);
            SMTTerm gtrueCase = addGuardIfNecessary(trueCase, universalVars);
            SMTTerm gfalseCase = addGuardIfNecessary(falseCase, universalVars);

            if (!cond.equals(gcond)) {
                ite.setCondition(gcond);
            }

            if (!trueCase.equals(gtrueCase)) {
                ite.setTrueCase(gtrueCase);
            }

            if (!falseCase.equals(gfalseCase)) {
                ite.setFalseCase(gfalseCase);
            }


        }
    }


    /**
     * Searches for non ground terms in sub, and stores them in terms. Begin with empty lists.
     *
     * @param terms list where the terms are stored
     * @param sub the term to be searched
     * @param universalVars universal variables
     * @param existentialVars existential variables
     * @param bind variables bounded by the current quantifier
     */
    public void searchArithTerms(Set<SMTTerm> terms, SMTTerm sub,
            Set<SMTTermVariable> universalVars, Set<SMTTermVariable> existentialVars,
            List<SMTTermVariable> bind) {

        if (sub instanceof SMTTermMultOp tm) {
            for (SMTTerm t : tm.getSubs()) {
                searchArithTerms(terms, t, universalVars, existentialVars, bind);
            }
            if (isArithmeticOperator(tm.getOperator())
                    && acceptableTerm(tm, universalVars, existentialVars, bind)) {
                terms.add(tm);
            }
        } else if (sub instanceof SMTTermCall tc) {
            for (SMTTerm t : tc.getArgs()) {
                searchArithTerms(terms, t, universalVars, existentialVars, bind);
            }
        } else if (sub instanceof SMTTermQuant tq) {
            searchArithTerms(terms, tq.getSub(), universalVars, existentialVars, bind);
        } else if (sub instanceof SMTTermITE ite) {
            searchArithTerms(terms, ite.getCondition(), universalVars, existentialVars, bind);
            searchArithTerms(terms, ite.getTrueCase(), universalVars, existentialVars, bind);
            searchArithTerms(terms, ite.getFalseCase(), universalVars, existentialVars, bind);
        } else if (sub instanceof SMTTermUnaryOp tu) {
            searchArithTerms(terms, tu.getSub(), universalVars, existentialVars, bind);
        }

    }

    /**
     * Searches for arithmetical ground terms in sub and stores them in terms
     */
    public void searchArithGroundTerms(Set<SMTTerm> terms, SMTTerm sub) {

        if (sub instanceof SMTTermMultOp tm) {
            for (SMTTerm t : tm.getSubs()) {
                searchArithGroundTerms(terms, t);
            }
            if (isArithmeticOperator(tm.getOperator()) && !containsVars(tm)) {
                terms.add(tm);
            }
        } else if (sub instanceof SMTTermCall tc) {
            for (SMTTerm t : tc.getArgs()) {
                searchArithGroundTerms(terms, t);
            }
        } else if (sub instanceof SMTTermQuant tq) {
            searchArithGroundTerms(terms, tq.getSub());
        } else if (sub instanceof SMTTermITE ite) {
            searchArithGroundTerms(terms, ite.getCondition());
            searchArithGroundTerms(terms, ite.getTrueCase());
            searchArithGroundTerms(terms, ite.getFalseCase());
        } else if (sub instanceof SMTTermUnaryOp tu) {
            searchArithGroundTerms(terms, tu.getSub());
        }

    }

    private boolean acceptableTerm(SMTTermMultOp tm, Set<SMTTermVariable> universalVars,
            Set<SMTTermVariable> existentialVars, List<SMTTermVariable> bind) {

        boolean known = true;
        boolean relevant = false;

        Set<SMTTerm> vars = new HashSet<>();
        getVariables(tm, vars);

        for (SMTTerm v : vars) {
            if (!universalVars.contains(v) && !existentialVars.contains(v)) {
                known = false;
            }
            if (bind.contains(v)) {
                relevant = true;
            }
        }
        return known && relevant;
    }


    private void getVariables(SMTTerm term, Set<SMTTerm> vars) {
        if (term instanceof SMTTermMultOp tm) {
            for (SMTTerm t : tm.getSubs()) {
                getVariables(t, vars);
            }


        } else if (term instanceof SMTTermCall tc) {
            for (SMTTerm t : tc.getArgs()) {
                getVariables(t, vars);
            }

        } else if (term instanceof SMTTermQuant tq) {
            getVariables(tq.getSub(), vars);
        } else if (term instanceof SMTTermITE ite) {
            getVariables(ite.getTrueCase(), vars);
            getVariables(ite.getFalseCase(), vars);
            getVariables(ite.getCondition(), vars);
        } else if (term instanceof SMTTermUnaryOp tu) {
            getVariables(tu.getSub(), vars);
        } else if (term instanceof SMTTermVariable) {
            vars.add(term);
        }

    }

    private boolean containsVars(SMTTerm term) {

        if (term instanceof SMTTermMultOp tm) {
            for (SMTTerm t : tm.getSubs()) {
                if (containsVars(t)) {
                    return true;
                }
            }

            return false;

        } else if (term instanceof SMTTermCall tc) {
            for (SMTTerm t : tc.getArgs()) {
                if (containsVars(t)) {
                    return true;
                }
            }
            return false;
        } else if (term instanceof SMTTermQuant tq) {
            return containsVars(tq.getSub());
        } else if (term instanceof SMTTermITE ite) {
            return containsVars(ite.getCondition()) || containsVars(ite.getTrueCase())
                    || containsVars(ite.getFalseCase());
        } else if (term instanceof SMTTermUnaryOp tu) {
            return containsVars(tu.getSub());
        } else {
            return term instanceof SMTTermVariable;
        }

    }

    private void classifySubs(Set<SMTTermVariable> universalVars, Set<SMTTerm> subs,
            Set<SMTTerm> universalSubs, Set<SMTTerm> existentialSubs) {
        for (SMTTerm sub : subs) {

            if (isUniversalSub(sub, universalVars)) {
                universalSubs.add(sub);
            } else {
                existentialSubs.add(sub);
            }


        }
    }


    private boolean isUniversalSub(SMTTerm t, Set<SMTTermVariable> universalVars) {

        if (t instanceof SMTTermMultOp tm) {
            for (SMTTerm sub : tm.getSubs()) {
                if (universalVars.contains(sub) || isUniversalSub(sub, universalVars)) {
                    return true;
                }
            }
        }
        return false;
    }
}
