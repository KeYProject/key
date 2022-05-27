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
    protected Term high;
    protected Term index;
    protected Term guard;
    protected Set<Term> arrays = new HashSet<>();
    protected Set<Term> oldDepPreds = new HashSet<>();
    protected Set<Term> allDepPreds = new HashSet<>();
    protected Set<Term> oldCompPreds = new HashSet<>();
    protected Set<Term> allCompPreds = new HashSet<>();

    public AbstractLoopInvariantGenerator(Sequent sequent, Services s) {
        seq = sequent;
        ruleApp = new RuleApplication(s, seq);
        services = ruleApp.services;
        tb = services.getTermBuilder();
        intLDT = services.getTypeConverter().getIntegerLDT();
    }

    protected void abstractGoal(Goal currentGoal) {
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

        for (Term cp : allCompPreds) {
            currentGoal.addFormula(new SequentFormula(cp), true, false);
//			currentGoal.addFormula(new SequentFormula(cp), false, false);
        }

        for (Term cp : allDepPreds) {
            currentGoal.addFormula(new SequentFormula(cp), true, false);
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

    protected void getIndexAndHigh(Sequent seq) {
        Expression high = null, index = null;
        for (final SequentFormula sf : seq.succedent()) {
            final Term formula = skipUpdates(sf.formula());
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

    protected void getLoopGuard(Sequent seq) {
        Term guard = null;
        for (SequentFormula sf : seq.succedent()) {
            final Term formula = skipUpdates(sf.formula());
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

    protected Term skipUpdates(Term formula) {
        return formula.op() instanceof UpdateApplication ? UpdateApplication.getTarget(formula) : formula;
    }

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
            Term formula = skipUpdates(sf.formula());
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
                arrays.add(tb.var(v));
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
