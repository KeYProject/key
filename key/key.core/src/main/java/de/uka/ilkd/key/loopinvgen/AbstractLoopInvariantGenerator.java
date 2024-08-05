package de.uka.ilkd.key.loopinvgen;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.expression.operator.*;
import de.uka.ilkd.key.java.statement.While;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.ArraySort;
import de.uka.ilkd.key.proof.Goal;

import java.util.HashSet;
import java.util.Set;

public abstract class AbstractLoopInvariantGenerator {
    protected final Sequent seq;
    protected final Services services;
    protected final TermBuilder tb;
    protected final RuleApplication ruleApp;
    protected final IntegerLDT intLDT;
    protected Term low;
    protected Term lowOuter;
    protected Term lowInner;
    protected Term high;
    protected Term highOuter;
    protected Term highInner;
    protected Term index;
    protected Term indexOuter;
    protected Term indexInner;
    protected Term guard;
    protected Term[] arrays = new Term[1];//2 when two arrays and 1 when one array.
    protected int arraysIndex = 0;
    protected Set<Term> oldDepPreds = new HashSet<>();
    protected Set<Term> oldInnerDepPreds = new HashSet<>();
    protected Set<Term> oldOuterDepPreds = new HashSet<>();
    protected Set<Term> allDepPreds = new HashSet<>();

    protected Set<Term> innerDepPreds = new HashSet<>();
    protected Set<Term> outerDepPreds = new HashSet<>();
    protected Set<Term> oldCompPreds = new HashSet<>();
    protected Set<Term> oldInnerCompPreds = new HashSet<>();
    protected Set<Term> oldOuterCompPreds = new HashSet<>();
    protected Set<Term> allCompPreds = new HashSet<>();
    protected Set<Term> outerCompPreds = new HashSet<>();
    protected Set<Term> innerCompPreds = new HashSet<>();
    public AbstractLoopInvariantGenerator(Sequent sequent, Services s) {
        seq = sequent;
        ruleApp = new RuleApplication(s, seq);
        services = ruleApp.services;
        tb = services.getTermBuilder();
        intLDT = services.getTypeConverter().getIntegerLDT();
    }

    protected void abstractGoal(Goal currentGoal, Set<Term> compPredsSet, Set<Term> depPredsSet) {
//		System.out.println("Goal: " + currentGoal);
        for (SequentFormula cgsf : currentGoal.sequent().antecedent()) {
            PosInOccurrence p = new PosInOccurrence(cgsf, PosInTerm.getTopLevel(), true);
            currentGoal.removeFormula(p);
        }

        for(SequentFormula cgsf:currentGoal.sequent().succedent()) {
            PosInOccurrence p = new PosInOccurrence(cgsf, PosInTerm.getTopLevel(), false);
            if(!cgsf.formula().containsJavaBlockRecursive()) {
                currentGoal.removeFormula(p);
            }
        }

        for (Term cp : compPredsSet) {
            currentGoal.addFormula(new SequentFormula(cp), true, false);
//			currentGoal.addFormula(new SequentFormula(cp), false, false);
        }

        for (Term cp : depPredsSet) {
            currentGoal.addFormula(new SequentFormula(cp), true, false);
//			currentGoal.addFormula(new SequentFormula(cp), false, false);
        }
//		System.out.println("Modified Goal: " + currentGoal);
    }

    protected void abstractSequent(Sequent seq, Set<Term> compPredsSet, Set<Term> depPredsSet) {
//		System.out.println("Goal: " + currentGoal);
        for (SequentFormula cgsf : seq.antecedent()) {
            PosInOccurrence p = new PosInOccurrence(cgsf, PosInTerm.getTopLevel(), true);
            seq.removeFormula(p);
        }

        for(SequentFormula cgsf:seq.succedent()) {
            PosInOccurrence p = new PosInOccurrence(cgsf, PosInTerm.getTopLevel(), false);
            if(!cgsf.formula().containsJavaBlockRecursive()) {
                seq.removeFormula(p);
            }
        }

        for (Term cp : compPredsSet) {
            seq.addFormula(new SequentFormula(cp), true, false);
//			currentGoal.addFormula(new SequentFormula(cp), false, false);
        }

        for (Term cp : depPredsSet) {
            seq.addFormula(new SequentFormula(cp), true, false);
//			currentGoal.addFormula(new SequentFormula(cp), false, false);
        }
//		System.out.println("Modified Goal: " + currentGoal);
    }

    protected void getLow(Sequent seq) {
        for (SequentFormula sf : seq.succedent()) {
            Term formula = sf.formula();
            if (formula.op() instanceof UpdateApplication) {
                Term update = UpdateApplication.getUpdate(formula);
                if (update.op() instanceof ElementaryUpdate) {
                    this.low = update.sub(0);
                    break;
                }
            }
        }
    }

    protected void getLows(Sequent seq) {
        for (SequentFormula sf : seq.succedent()) {
            Term formula = sf.formula();
            if (formula.op() instanceof UpdateApplication) {
                Term update = UpdateApplication.getUpdate(formula);
                if(update.op().equals(UpdateJunctor.PARALLEL_UPDATE)) {
                    Term updateOuter = update.sub(0);
                    Term updateInner = update.sub(1);
                    if (updateOuter.op() instanceof ElementaryUpdate) {
                        this.lowOuter = updateOuter.sub(0);
//                        System.out.println("Low Outer: " + this.lowOuter);
                    }
                    if (updateInner.op() instanceof ElementaryUpdate) {
                        this.lowInner = updateInner.sub(0);
//                        System.out.println("Low Inner: " + this.lowInner);
                    }
                    break;
                }
            }
        }
    }
    protected void getIndexAndHigh(Sequent seq) {
        Expression high = null, index = null;
        for (final SequentFormula sf : seq.succedent()) {
            final Term formula = tb.goBelowUpdates(sf.formula());
            if (formula.op() == Modality.DIA) {
                ProgramElement pe = formula.javaBlock().program();
                Statement activePE;
                if (pe instanceof ProgramPrefix) {
                    activePE = (Statement) ((ProgramPrefix) pe).getLastPrefixElement().getFirstElement();
                } else {
                    activePE = (Statement) pe.getFirstElement();
                }
                if (activePE instanceof While) {
                    final Expression expr = ((While) activePE).getGuardExpression();
                    if (expr instanceof GreaterOrEquals || expr instanceof GreaterThan) {
                        high = ((ComparativeOperator) expr).getExpressionAt(0);
                        index = ((ComparativeOperator) expr).getExpressionAt(1);
                    } else if (expr instanceof LessOrEquals || expr instanceof LessThan) {
                        high = ((ComparativeOperator) expr).getExpressionAt(1);
                        index = ((ComparativeOperator) expr).getExpressionAt(0);
                    }
                }
                break;
            }
        }
        this.high = expr2term(high);
        this.index = expr2term(index);
    }

    protected void getIndexesAndHighs(Sequent seq) {
        Expression highInner = null, indexInner = null;
        Expression highOuter = null, indexOuter = null;
        for (final SequentFormula sf : seq.succedent()) {
            final Term formula = tb.goBelowUpdates(sf.formula());
            if (formula.op() == Modality.DIA) {
                ProgramElement pe = formula.javaBlock().program();
                Statement activePE;
                if (pe instanceof ProgramPrefix) {
                    activePE = (Statement) ((ProgramPrefix) pe).getLastPrefixElement().getFirstElement();
                } else {
                    activePE = (Statement) pe.getFirstElement();
                }
                if (activePE instanceof While) {
                    final Expression expr = ((While) activePE).getGuardExpression();
                    if (expr instanceof GreaterOrEquals || expr instanceof GreaterThan) {
                        highOuter = ((ComparativeOperator) expr).getExpressionAt(0);
                        indexOuter = ((ComparativeOperator) expr).getExpressionAt(1);
                    } else if (expr instanceof LessOrEquals || expr instanceof LessThan) {
                        highOuter = ((ComparativeOperator) expr).getExpressionAt(1);
                        indexOuter = ((ComparativeOperator) expr).getExpressionAt(0);
                    }
                    final Statement stmtInner = ((While) activePE).getBody();
                    if (stmtInner.getFirstElement() instanceof While) {
                        final Expression exprInner = ((While) stmtInner.getFirstElement() ).getGuardExpression();
                        if (exprInner instanceof GreaterOrEquals || exprInner instanceof GreaterThan) {
                            highInner = ((ComparativeOperator) exprInner).getExpressionAt(0);
                            indexInner = ((ComparativeOperator) exprInner).getExpressionAt(1);
                        } else if (exprInner instanceof LessOrEquals || exprInner instanceof LessThan) {
                            highInner = ((ComparativeOperator) exprInner).getExpressionAt(1);
                            indexInner = ((ComparativeOperator) exprInner).getExpressionAt(0);
                        }
                    }
                }
                break;
            }
        }
        this.highOuter = expr2term(highOuter);
        this.indexOuter = expr2term(indexOuter);
        this.highInner = expr2term(highInner);
        this.indexInner = expr2term(indexInner);
//        System.out.println("High Inner: " + this.highInner);
//        System.out.println("High Outer: " + this.highOuter);
//        System.out.println("Index Inner: " + this.indexInner);
//        System.out.println("index Outer: " + this.indexOuter);
    }

    protected Set<Term> getInnerLocSets(){
        Set<Term> arr=new HashSet<>();
        for(Term a:arrays) {
            arr.add(tb.arrayRange(a, this.lowInner, this.highInner));
        }
        return arr;
    }

    protected Set<Term> getOuterLocSets(){
        Set<Term> arr=new HashSet<>();
        for(Term a:arrays) {
            arr.add(tb.arrayRange(a, this.lowOuter, this.highOuter));
        }
        return arr;
    }
    protected void getLoopGuard(Sequent seq) {
        Term guard = null;
        for (SequentFormula sf : seq.succedent()) {
            final Term formula = tb.goBelowUpdates(sf.formula());
            if (formula.op() == Modality.DIA) {
                ProgramElement pe = formula.javaBlock().program();
                Statement activePE;
                if (pe instanceof ProgramPrefix) {
                    activePE = (Statement) ((ProgramPrefix) pe).getLastPrefixElement().getFirstElement();
                } else {
                    activePE = (Statement) pe.getFirstElement();
                }
                if (activePE instanceof While) {
                    final Expression expr = ((While) activePE).getGuardExpression();
                    final Term left = expr2term(((ComparativeOperator) expr).getExpressionAt(0));
                    final Term right = expr2term(((ComparativeOperator) expr).getExpressionAt(1));
                    if (expr instanceof GreaterOrEquals) {
                        guard = tb.geq(left, right);
                    } else if (expr instanceof GreaterThan) {
                        guard = tb.gt(left, right);
                    } else if (expr instanceof LessOrEquals) {
                        guard = tb.leq(left, right);
                    } else if (expr instanceof LessThan) {
                        guard = tb.lt(left,	right);
                    }

                }
                break;
            }
        }
        this.guard = guard;
    }

    protected Term expr2term(Expression expr) {
        return this.services.getTypeConverter().convertToLogicElement(expr);
    }

//    protected Term skipUpdates(Term formula) {
//        return formula.op() instanceof UpdateApplication ? UpdateApplication.getTarget(formula) : formula;
//    }

    protected Set<LocationVariable> extractProgramVariable(Statement s) {
        ProgramVariableCollectorWithArrayIndices pvc = new ProgramVariableCollectorWithArrayIndices(s, services);
        pvc.start();
//		System.out.println(pvc.result());
//		System.out.println("my array: " + pvc.array());
//		System.out.println(pvc.index());
        return pvc.result();
    }

    protected void getLocSet(Sequent seq) {
        // How to find the targeted location set (the array)?
        for (SequentFormula sf : seq.succedent()) {
            Term formula = tb.goBelowUpdates(sf.formula());
            if (formula.op() == Modality.DIA) {
                Statement activePE = (Statement) formula.javaBlock().program();
                Set<LocationVariable> lvs = extractProgramVariable(activePE);
                findArray(lvs);
            }
        }
    }

    protected void findArray(Set<LocationVariable> set) {

        for (LocationVariable v : set) {
            if (v.sort() instanceof ArraySort) {
                // System.out.println(v + " is an array with element sort " + ((ArraySort)
                // v.sort()).elementSort());
                // KeYJavaType kjt = v.getKeYJavaType(services);
                // kjt.getSort(); // logic sort
                // kjt.getJavaType(); // Java type
                // System.out.println(v + " is of KeY sort " + kjt.getSort());
                // System.out.println(v + " is of java type " + kjt.getJavaType());
//				System.out.println("old array: " + v);
                arrays[arraysIndex]=tb.var(v);
                arraysIndex++;
            }
        }
    }

    protected boolean isComparisonOperator(Term pred) {
        final boolean isComparison =
                pred.op() == intLDT.getLessThan() ||
                        pred.op() == intLDT.getGreaterThan() ||
                        pred.op() == intLDT.getLessOrEquals() ||
                        pred.op() == intLDT.getGreaterOrEquals() ||
                        pred.op() == Equality.EQUALS;
        return isComparison;
    }

    public abstract LoopInvariantGenerationResult generate();
}
