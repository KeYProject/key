/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.loopinvgen;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.DependenciesLDT;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.ldt.LocSetLDT;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.equality.RenamingTermProperty;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.JFunction;
import de.uka.ilkd.key.logic.op.Operator;

import org.key_project.util.collection.Pair;

public class PredicateSetCompressor {
    private final DependenciesLDT depLDT;
    private final TermBuilder tb;
    // private final SequentFormula currentIdxF;
    private final IntegerLDT intLDT;
    private final LocSetLDT locSetLDT;

    private Set<Operator> comparisonPredicateSymbols = new HashSet<>();
    private final JFunction lt, leq, gt, geq;
    private final SideProof sProof;
    private final boolean ailias;
    private Set<Term> allPreds;

    public PredicateSetCompressor(Set<Term> preds, Sequent seq, boolean ailiasing,
            Services services) {
        tb = services.getTermBuilder();
        // currentIdxF = currentIndexFormula;
        depLDT = services.getTypeConverter().getDependenciesLDT();
        intLDT = services.getTypeConverter().getIntegerLDT();

        lt = intLDT.getLessThan();
        comparisonPredicateSymbols.add(lt);
        leq = intLDT.getLessOrEquals();
        comparisonPredicateSymbols.add(leq);
        gt = intLDT.getGreaterThan();
        comparisonPredicateSymbols.add(gt);
        geq = intLDT.getGreaterOrEquals();
        comparisonPredicateSymbols.add(geq);

        sProof = new SideProof(services, seq, 5000);// 75000
        ailias = ailiasing;
        allPreds = preds;
        locSetLDT = new LocSetLDT(services);
    }

    public Set<Term> compress() {

        Set<Term> compPredsList = new HashSet<>();
        Set<Term> depPredsList = new HashSet<>();
        Set<Term> result = new HashSet<>();
        for (Term term : allPreds) {
            if (term.op().equals(depLDT.getNoR()) || term.op().equals(depLDT.getNoW())
                    || term.op().equals(depLDT.getNoRaW()) || term.op().equals(depLDT.getNoWaR())
                    || term.op().equals(depLDT.getNoWaW()) ||
                    term.op().equals(depLDT.getRelaxedNoR())
                    || term.op().equals(depLDT.getRelaxedNoW())
                    || term.op().equals(depLDT.getRelaxedNoRaW())
                    || term.op().equals(depLDT.getRelaxedNoWaR())
                    || term.op().equals(depLDT.getRelaxedNoWaW())) {
                depPredsList.add(term);
            } else if (term.op().equals(lt) || term.op().equals(leq) || term.op().equals(gt)
                    || term.op().equals(geq)
                    || term.op().equals(Equality.EQUALS)) {
                compPredsList.add(term);
            } else
                result.add(term);
        }
        result.addAll(finalCompPredListCompression(compPredsList));
        // result.addAll(compPredsList);
        result.addAll(depPredListCompressionByPredicate(depPredListCompressionBySET(depPredsList)));
        return result;

    }

    private Set<Term> depPredListCompressionBySET(Set<Term> fDepPredList) {
        Set<Term> toDelete = new HashSet<>();
        Set<Term> toAdd = new HashSet<>();
        for (Term depPred1 : fDepPredList) {
            for (Term depPred2 : fDepPredList) {
                if (depPred1.op() == depPred2.op() && depPred1.sub(0) != depPred2.sub(0)) {
                    if (sProof.proofSubSet(depPred1.sub(0), depPred2.sub(0))) {
                        toDelete.add(depPred1);
                    }
                    // else if(sProof.proofSubSet(depPred2.sub(0), depPred1.sub(0)) &&
                    // depPred1.sub(0)!=depPred2.sub(0)){
                    // toDelete.add(depPred2);
                    // }
                    else if (depPred1.sub(0).op() == locSetLDT.getArrayRange()
                            && depPred2.sub(0).op() == locSetLDT.getArrayRange()) {
                        if (depPred1.sub(0).sub(0) == depPred2.sub(0).sub(0)
                                && depPred1.sub(0).sub(2) == depPred2.sub(0).sub(1)) {
                            toDelete.add(depPred1);
                            toDelete.add(depPred2);
                            if (depPred1.op() == depLDT.getNoR()) {
                                toAdd.add(tb.noR(
                                    tb.arrayRange(depPred1.sub(0).sub(0), depPred1.sub(0).sub(1),
                                        depPred2.sub(0).sub(2))));
                            } else if (depPred1.op() == depLDT.getNoRaW()) {
                                toAdd.add(tb.noRaW(
                                    tb.arrayRange(depPred1.sub(0).sub(0), depPred1.sub(0).sub(1),
                                        depPred2.sub(0).sub(2))));
                            } else if (depPred1.op() == depLDT.getNoWaR()) {
                                toAdd.add(tb.noWaR(
                                    tb.arrayRange(depPred1.sub(0).sub(0), depPred1.sub(0).sub(1),
                                        depPred2.sub(0).sub(2))));
                            } else if (depPred1.op() == depLDT.getNoWaW()) {
                                toAdd.add(tb.noWaW(
                                    tb.arrayRange(depPred1.sub(0).sub(0), depPred1.sub(0).sub(1),
                                        depPred2.sub(0).sub(2))));
                            } else if (depPred1.op() == depLDT.getNoW()) {
                                toAdd.add(tb.noW(
                                    tb.arrayRange(depPred1.sub(0).sub(0), depPred1.sub(0).sub(1),
                                        depPred2.sub(0).sub(2))));
                            }
                        } else if (depPred1.sub(0).op() == locSetLDT.getMatrixRange()
                                && depPred2.sub(0).op() == locSetLDT.getMatrixRange()) {
                            if (sProof.proofSubSet(depPred1.sub(0), depPred2.sub(0))) {
                                toDelete.add(depPred1);
                            }

                        }
                    }
                }
            }
        }
        fDepPredList.addAll(toAdd);
        fDepPredList.removeAll(toDelete);

        toDelete.clear();
        // if (ailias) {
        // for (Term depPred1 : fDepPredList) {
        // for (Term depPred2 : fDepPredList) {
        // if (depPred1.op().equals(depPred2.op()) && depPred1.sub(0).sub(0) !=
        // depPred2.sub(0).sub(0)) {
        // if (sProof.proofEquality(depPred1.sub(0), depPred2.sub(0))) {
        // if (!toDelete.contains(depPred2)) {
        // toDelete.add(depPred1);
        // break;// depPred1 is already deleted
        // }
        // }
        // }
        // }
        // }
        // }

        // System.out.println("DepPreds 2 Deleted by Compressor " + fDepPredList);
        return fDepPredList;
    }

    private Set<Term> depPredListCompressionByPredicate(Set<Term> fDepPredList) {
        Set<Term> toDelete = new HashSet<>();
        // HashMap<Term, Boolean> depPreds= new HashMap<Term, Boolean>();
        //
        // for(Term d : fDepPredList){
        // depPreds.put(d, false);
        // }
        for (Term depPred1 : fDepPredList) {
            for (Term depPred2 : fDepPredList) {
                if (toDelete.contains(depPred2)) { // CHECK method for more efficient optimisations,
                                                   // e.g. exclude
                    // deleted terms also from being considered for depPred1
                    continue;
                }

                if (depPred1.op().equals(depLDT.getNoR())) {
                    if (depPred2.op().equals(depLDT.getNoRaW())
                            || depPred2.op().equals(depLDT.getNoWaR())) {
                        if (sProof.proofSubSet(depPred2.sub(0), depPred1.sub(0))) {
                            toDelete.add(depPred2);
                        }
                    }
                } else if (depPred1.op().equals(depLDT.getNoW())) {
                    if (depPred2.op().equals(depLDT.getNoRaW())
                            || depPred2.op().equals(depLDT.getNoWaR())
                            || depPred2.op().equals(depLDT.getNoWaW())) {
                        if (sProof.proofSubSet(depPred2.sub(0), depPred1.sub(0))) {
                            toDelete.add(depPred2);
                        }
                    }
                } else if (depPred1.op().equals(depLDT.getRelaxedNoR())) {
                    if (depPred2.op().equals(depLDT.getRelaxedNoRaW())
                            || depPred2.op().equals(depLDT.getRelaxedNoWaR())) {
                        if (sProof.proofSubSet(depPred2.sub(0), depPred1.sub(0))) {
                            toDelete.add(depPred2);
                        }
                    }
                } else if (depPred1.op().equals(depLDT.getRelaxedNoW())) {
                    if (depPred2.op().equals(depLDT.getRelaxedNoRaW())
                            || depPred2.op().equals(depLDT.getRelaxedNoWaR())
                            || depPred2.op().equals(depLDT.getRelaxedNoWaW())) {
                        if (sProof.proofSubSet(depPred2.sub(0), depPred1.sub(0))) {
                            toDelete.add(depPred2);
                        }
                    }
                }

                if (depPred1.op() == depPred2.op()
                        && !sProof.proofEquality(depPred2.sub(0), depPred1.sub(0))) {
                    if (sProof.proofSubSet(depPred2.sub(0), depPred1.sub(0))) {
                        toDelete.add(depPred2);
                    }
                }


            }
        }

        fDepPredList.removeAll(toDelete);
        // System.out.println("DepPreds Deleted by Compressor: "+toDelete);
        return fDepPredList;
    }

    private boolean isEqualityProvable(Term left, Term right) {
        return left.equalsModProperty(right, RenamingTermProperty.RENAMING_TERM_PROPERTY)
                || sProof.proofEquality(left, right);
    }

    private Set<Term> finalCompPredListCompression(Set<Term> fCompPredList) {
        Set<Term> toDelete = new HashSet<>();
        Set<Term> toAdd = new HashSet<>();
        HashMap<Pair<Term, Term>, Boolean> cache = new HashMap<>();
        for (Term compPred1 : fCompPredList) {
            for (Term compPred2 : fCompPredList) {
                final boolean leftSidesEqualityProvable =
                    isEqualityProvable(cache, compPred1.sub(0), compPred2.sub(0));
                final boolean rightSidesEqualityProvable =
                    isEqualityProvable(cache, compPred1.sub(1), compPred2.sub(1));

                if (leftSidesEqualityProvable && rightSidesEqualityProvable) { // a X b
                    // && a
                    // Y b
                    if (compPred1.op().equals(geq) && compPred2.op().equals(gt)) {
                        if (!toDelete.contains(compPred1)) {
                            // System.out.println("Compression deleted: " + compPred2 + " because of
                            // " + compPred1);
                            toDelete.add(compPred2);

                        }
                    } else if (compPred1.op().equals(leq) && compPred2.op().equals(lt)) {
                        if (!toDelete.contains(compPred1)) {
                            // System.out.println("1- Compression deleted: " + compPred2 + " because
                            // of " + compPred1);
                            toDelete.add(compPred2);
                        }
                    } else if (compPred1.op().equals(Equality.EQUALS)
                            && compPred2.op().equals(geq)) {
                        if (!toDelete.contains(compPred2)) {
                            // System.out.println("2- Compression deleted: " + compPred1 + " because
                            // of " + compPred2);
                            toDelete.add(compPred1);
                        }
                    } else if (compPred1.op().equals(Equality.EQUALS)
                            && compPred2.op().equals(leq)) {
                        if (!toDelete.contains(compPred2)) {
                            // System.out.println("3- Compression deleted: " + compPred2 + " because
                            // of " + compPred1);
                            toDelete.add(compPred1);
                        }
                    }
                    // else if (compPred1.op().equals(gt) && compPred2.op().equals(lt)) { //There
                    // should not be such a case because this means the inv is wrong
                    // toDelete.add(compPred1);
                    // toDelete.add(compPred2);
                    // }
                    else if (compPred1.op().equals(geq) && compPred2.op().equals(leq)) {
                        toDelete.add(compPred1);
                        toDelete.add(compPred2);
                        toAdd.add(tb.equals(compPred1.sub(0), compPred1.sub(1)));
                    }

                } else if (isEqualityProvable(compPred1.sub(0), compPred2.sub(1))
                        && isEqualityProvable(compPred1.sub(1), compPred2.sub(0))) { // a
                    // X
                    // b
                    // &&
                    // b
                    // Y
                    // a
                    if (compPred1.op().equals(gt) && compPred2.op().equals(lt)) {
                        if (!toDelete.contains(compPred2)) {
                            // System.out.println("4- Compression deleted: " + compPred1 + " because
                            // of " + compPred2);
                            toDelete.add(compPred1);
                        }
                    } else if (compPred1.op().equals(geq) && compPred2.op().equals(lt)) {
                        if (!toDelete.contains(compPred1)) {
                            // System.out.println("5- Compression deleted: " + compPred2 + " because
                            // of " + compPred1);
                            toDelete.add(compPred2);
                        }
                    } else if (compPred1.op().equals(leq) && compPred2.op().equals(gt)) {
                        if (!toDelete.contains(compPred1)) {
                            // System.out.println("6- Compression deleted: " + compPred2 + " because
                            // of " + compPred1);
                            toDelete.add(compPred2);
                        }
                    } else if (compPred1.op().equals(geq) && compPred2.op().equals(leq)) {
                        if (!toDelete.contains(compPred2)) {
                            // System.out.println("7- Compression deleted: " + compPred1 + " because
                            // of " + compPred2);
                            toDelete.add(compPred1);
                        }
                    } else if (compPred1.op().equals(Equality.EQUALS)
                            && compPred2.op().equals(geq)) {
                        if (!toDelete.contains(compPred2)) {
                            // System.out.println("8- Compression deleted: " + compPred1 + " because
                            // of " + compPred2);
                            toDelete.add(compPred1);
                        }
                    } else if (compPred1.op().equals(Equality.EQUALS)
                            && compPred2.op().equals(leq)) {
                        if (!toDelete.contains(compPred2)) {
                            // System.out.println("9- Compression deleted: " + compPred1 + " because
                            // of " + compPred2);
                            toDelete.add(compPred1);
                        }
                    }
                }
                // else if (leftSidesEqualityProvable && !rightSidesEqualityProvable) {
                // if ((compPred1.op() == lt && compPred2.op() == lt)
                // || (compPred1.op() == lt && compPred2.op() == leq)) {
                // if (sProof.proofLT(compPred1.sub(1), compPred2.sub(1))) {
                // if (!toDelete.contains(compPred1)) {
                // System.out.println("10- Compression deleted: " + compPred1 + " because of " +
                // compPred2);
                // toDelete.add(compPred2);
                // }
                // } else if(sProof.proofGEQ(compPred1.sub(1), compPred2.sub(1))) {
                // if (!toDelete.contains(compPred1)) {
                // System.out.println("11- Compression deleted: " + compPred2 + " because of " +
                // compPred1);
                // toDelete.add(compPred2);
                // }
                // }
                // } else if ((compPred1.op() == gt && compPred2.op() == gt)
                // || (compPred1.op() == gt && compPred2.op() == geq)) {
                // if (sProof.proofLT(compPred1.sub(1), compPred2.sub(1))) {
                // if (!toDelete.contains(compPred1)) {
                // System.out.println("12- Compression deleted: " + compPred2 + " because of " +
                // compPred1);
                // toDelete.add(compPred2);
                // }
                // } else {
                // if (!toDelete.contains(compPred2)) {
                // System.out.println("13- Compression deleted: " + compPred1 + " because of " +
                // compPred2);
                // toDelete.add(compPred1);
                // }
                // }
                // } else if ((compPred1.op() == leq && compPred2.op() == leq)
                // || (compPred1.op() == leq && compPred2.op() == lt)) {
                // if (sProof.proofLT(compPred1.sub(1), compPred2.sub(1))) {
                // if (!toDelete.contains(compPred2)) {
                // System.out.println("14- Compression deleted: " + compPred1 + " because of " +
                // compPred2);
                // toDelete.add(compPred1);
                // }
                // } else if(sProof.proofGEQ(compPred1.sub(1), compPred2.sub(1))) {
                // if (!toDelete.contains(compPred1)) {
                // System.out.println("15- Compression deleted: " + compPred2 + " because of " +
                // compPred1);
                // toDelete.add(compPred2);
                // }
                // }
                // }
                // else if ((compPred1.op() == geq && compPred2.op() == geq)
                // || (compPred1.op() == gt && compPred2.op() == gt)) {
                // if (sProof.proofLT(compPred1.sub(1), compPred2.sub(1))) {
                // if (!toDelete.contains(compPred1)) {
                // System.out.println("16- Compression deleted: " + compPred2 + " because of " +
                // compPred1);
                // toDelete.add(compPred2);
                // }
                // } else if(sProof.proofGEQ(compPred1.sub(1), compPred2.sub(1))) {
                // if (!toDelete.contains(compPred2)) {
                // System.out.println("17- Compression deleted: " + compPred1 + " because of " +
                // compPred2);
                // toDelete.add(compPred1);
                // }
                // }
                // }
                // }
                // else if (compPred1.op() == compPred2.op() && rightSidesEqualityProvable &&
                // !leftSidesEqualityProvable) {
                // if (compPred1.op() == lt) {
                // if (sProof.proofLT(compPred1.sub(0), compPred2.sub(0))) {
                // if (!toDelete.contains(compPred1)) {
                // System.out.println("18- Compression deleted: " + compPred1 + " because of " +
                // compPred2);
                // toDelete.add(compPred2);
                // }
                // } else if(sProof.proofGEQ(compPred1.sub(0), compPred2.sub(0))) {
                // if (!toDelete.contains(compPred1)) {
                // System.out.println("19- Compression deleted: " + compPred2 + " because of " +
                // compPred1);
                // toDelete.add(compPred2);
                // }
                // }
                // } else if (compPred1.op() == gt) {
                // if (sProof.proofLT(compPred1.sub(0), compPred2.sub(0))) {
                // if (!toDelete.contains(compPred1)) {
                // System.out.println("20- Compression deleted: " + compPred2 + " because of " +
                // compPred1);
                // toDelete.add(compPred2);
                // }
                // } else if(sProof.proofGEQ(compPred1.sub(0), compPred2.sub(0))){
                // if (!toDelete.contains(compPred2)) {
                // System.out.println("21- Compression deleted: " + compPred1 + " because of " +
                // compPred2);
                // toDelete.add(compPred1);
                // }
                // }
                // } else if (compPred1.op() == leq) {
                // if (sProof.proofLT(compPred1.sub(0), compPred2.sub(0))) {
                // if (!toDelete.contains(compPred2)) {
                // System.out.println("22- Compression deleted: " + compPred1 + " because of " +
                // compPred2);
                // toDelete.add(compPred1);
                // }
                // } else if(sProof.proofGEQ(compPred1.sub(0), compPred2.sub(0))) {
                // if (!toDelete.contains(compPred1)) {
                // System.out.println("23- Compression deleted: " + compPred2 + " because of " +
                // compPred1);
                // toDelete.add(compPred2);
                // }
                // }
                // } else if (compPred1.op() == geq) {
                // if (sProof.proofLT(compPred1.sub(0), compPred2.sub(0))) {
                // if (!toDelete.contains(compPred1)) {
                // System.out.println("24- Compression deleted: " + compPred2 + " because of " +
                // compPred1);
                // toDelete.add(compPred2);
                // }
                // } else if(sProof.proofGEQ(compPred1.sub(0), compPred2.sub(0))) {
                // if (!toDelete.contains(compPred2)) {
                // System.out.println("25- Compression deleted: " + compPred1 + " because of " +
                // compPred2);
                // toDelete.add(compPred1);
                // }
                // }
                // }
                // }
            }
        }
        fCompPredList.removeAll(toDelete);
        // System.out.println("CompPreds Deleted by Compressor: " + toDelete);
        return fCompPredList;
    }

    private boolean isEqualityProvable(HashMap<Pair<Term, Term>, Boolean> cache, Term left,
            Term right) {
        final boolean isEqualityProvable;
        Pair<Term, Term> key = new Pair<>(left, right);
        Boolean result = cache.get(key);
        if (result != null) {
            isEqualityProvable = result;
        } else {
            key = new Pair<>(right, left);
            result = cache.get(key);
            if (result != null) {
                isEqualityProvable = result;
            } else {
                isEqualityProvable = isEqualityProvable(left, right);
                cache.put(key, isEqualityProvable);
            }
        }
        return isEqualityProvable;
    }
}
