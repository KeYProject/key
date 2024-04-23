/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.macros;

import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import de.uka.ilkd.key.control.UserInterfaceControl;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.ArrayDeclaration;
import de.uka.ilkd.key.java.declaration.ClassDeclaration;
import de.uka.ilkd.key.java.declaration.InterfaceDeclaration;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.SortCollector;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.JFunction;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.proof.rulefilter.RuleFilter;
import de.uka.ilkd.key.prover.ProverTaskListener;
import de.uka.ilkd.key.rule.OneStepSimplifier;
import de.uka.ilkd.key.rule.Rule;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.speclang.ClassAxiom;
import de.uka.ilkd.key.speclang.RepresentsAxiom;
import de.uka.ilkd.key.strategy.NumberRuleAppCost;
import de.uka.ilkd.key.strategy.RuleAppCost;
import de.uka.ilkd.key.strategy.RuleAppCostCollector;
import de.uka.ilkd.key.strategy.Strategy;
import de.uka.ilkd.key.strategy.TopRuleAppCost;
import de.uka.ilkd.key.strategy.feature.MutableState;

import org.key_project.logic.Name;
import org.key_project.logic.sort.Sort;
import org.key_project.util.collection.ImmutableList;

public abstract class AbstractBlastingMacro extends StrategyProofMacro {

    protected abstract RuleFilter getSemanticsRuleFilter();

    protected abstract RuleFilter getEqualityRuleFilter();

    protected abstract Set<String> getAllowedPullOut();

    @Override
    public ProofMacroFinishedInfo applyTo(UserInterfaceControl uic, Proof proof,
            ImmutableList<Goal> goals, PosInOccurrence posInOcc, ProverTaskListener listener)
            throws InterruptedException {
        for (Goal goal : goals) {
            addInvariantFormula(goal);
        }
        return super.applyTo(uic, proof, goals, posInOcc, listener);
    }

    protected void addInvariantFormula(Goal goal) {
        Sort nullSort = goal.proof().getServices().getTypeConverter().getHeapLDT().getNull().sort();

        SortCollector sortCollector = new SortCollector();

        for (SequentFormula sf : goal.sequent()) {
            sf.formula().execPreOrder(sortCollector);
        }

        Set<Sort> sorts = sortCollector.getSorts();
        sorts.remove(nullSort);
        List<SequentFormula> formulae = createFormulae(goal.proof().getServices(), sorts);
        for (SequentFormula sf : formulae) {
            Sequent s = goal.sequent();
            Semisequent antecedent = s.antecedent();
            if (!antecedent.containsEqual(sf)) {
                goal.addFormula(sf, true, true);
            }
        }
    }

    @Override
    protected Strategy createStrategy(Proof proof, PosInOccurrence posInOcc) {
        return new SemanticsBlastingStrategy();
    }

    private boolean containsSubTypes(Sort s, Set<Sort> sorts) {
        for (Sort st : sorts) {
            if (st.extendsTrans(s)) {
                return true;
            }
        }
        return false;
    }

    private List<SequentFormula> createFormulae(Services services, Set<Sort> sorts) {
        List<SequentFormula> result = new LinkedList<>();

        JavaInfo info = services.getJavaInfo();
        TermBuilder tb = new TermBuilder(services.getTermFactory(), services);
        SpecificationRepository spec = services.getSpecificationRepository();

        Sort heapSort = services.getTypeConverter().getHeapLDT().targetSort();

        LogicVariable h = new LogicVariable(new Name("h"), heapSort);

        for (KeYJavaType kjt : info.getAllKeYJavaTypes()) {

            Sort sort = kjt.getSort();

            if (!containsSubTypes(sort, sorts)) {
                continue;
            }

            if (!(kjt.getJavaType() instanceof ClassDeclaration
                    || kjt.getJavaType() instanceof InterfaceDeclaration
                    || kjt.getJavaType() instanceof ArrayDeclaration)) {
                continue;
            }

            LogicVariable o = new LogicVariable(new Name("o"), kjt.getSort());
            for (ClassAxiom c : spec.getClassAxioms(kjt)) {
                if (c instanceof RepresentsAxiom && c.getKJT().equals(kjt)) {
                    addFormulas(result, kjt, c, o, h, services);
                }
            }
        }
        return result;
    }

    private static void addFormulas(List<SequentFormula> result, KeYJavaType kjt, ClassAxiom c,
            LogicVariable o, LogicVariable h, Services services) {
        TermBuilder tb = new TermBuilder(services.getTermFactory(), services);
        Term exactInstance = tb.exactInstance(kjt.getSort(), tb.var(o));
        RepresentsAxiom ra = (RepresentsAxiom) c;

        try {
            Term t = ra.getAxiom(h, ra.getTarget().isStatic() ? null : o, services);
            if (t.op().equals(Equality.EQV)) {
                Term left = t.sub(0);
                Term right = t.sub(1);

                Term equivalence = t;
                Term implication;

                Term[] heaps = new Term[1];
                heaps[0] = tb.var(h);

                Term inv = tb.inv(heaps, tb.var(o));

                if (left.op().name().equals(inv.op().name())) {

                    implication = tb.imp(left, right);

                    Term exactInstanceEquiv = tb.imp(exactInstance, equivalence);
                    Term instanceImpl = implication;

                    exactInstanceEquiv = tb.all(h, tb.all(o, exactInstanceEquiv));
                    instanceImpl = tb.all(h, tb.all(o, instanceImpl));

                    result.add(new SequentFormula(exactInstanceEquiv));

                    if (!right.equals(tb.tt())) {
                        result.add(new SequentFormula(instanceImpl));
                    }
                } else if (right.op().name().equals(inv.op().name())) {

                    Term exactInstanceEquiv = tb.imp(exactInstance, equivalence);
                    implication = tb.imp(right, left);
                    Term instanceImpl = implication;

                    exactInstanceEquiv = tb.all(h, tb.all(o, exactInstanceEquiv));
                    instanceImpl = tb.all(h, tb.all(o, instanceImpl));

                    result.add(new SequentFormula(exactInstanceEquiv));

                    if (!left.equals(tb.tt())) {
                        result.add(new SequentFormula(instanceImpl));
                    }

                } else {
                    Term f = t;
                    f = tb.all(h, tb.all(o, f));
                    result.add(new SequentFormula(f));
                }
            } else {
                Term f = t;
                f = tb.all(h, tb.all(o, f));
                result.add(new SequentFormula(f));
            }
        } catch (Exception e) {
        }
    }

    private class SemanticsBlastingStrategy implements Strategy {

        @Override
        public Name name() {
            return new Name("Semantics Blasting");
        }

        @Override
        public RuleAppCost computeCost(RuleApp app, PosInOccurrence pio, Goal goal,
                MutableState mState) {

            if (app.rule() instanceof OneStepSimplifier) {
                return NumberRuleAppCost.getZeroCost();
            }
            // else if(app.rule().name().toString().equals("applyEq")){
            // return LongRuleAppCost.ZERO_COST;
            // }
            else if (getSemanticsRuleFilter().filter(app.rule())) {
                return NumberRuleAppCost.create(1);
            } else if (getEqualityRuleFilter().filter(app.rule())) {
                return NumberRuleAppCost.create(10);
            } else if (app.rule().name().toString().equals("pullOut")) {
                Term t = pio.subTerm();
                if (t.op() instanceof JFunction) {
                    if (getAllowedPullOut().contains(t.op().name().toString())) {
                        return NumberRuleAppCost.create(1000);
                    }
                }

            }

            return TopRuleAppCost.INSTANCE;
        }

        @Override
        public boolean isApprovedApp(RuleApp app, PosInOccurrence pio, Goal goal) {

            if (app.rule() instanceof OneStepSimplifier) {
                return true;
            }

            Rule rule = app.rule();

            String name = rule.name().toString();


            return name.equals("pullOut")
                    // ||name.startsWith("applyEq")
                    || getSemanticsRuleFilter().filter(rule)
                    || getEqualityRuleFilter().filter(rule);

        }

        @Override
        public void instantiateApp(RuleApp app, PosInOccurrence pio, Goal goal,
                RuleAppCostCollector collector) {
        }

        @Override
        public boolean isStopAtFirstNonCloseableGoal() {
            return false;
        }

    }

}
