/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule;

import javax.annotation.Nonnull;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.statement.While;
import de.uka.ilkd.key.java.visitor.ProgramElementReplacer;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.Transformer;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.metaconstruct.ForToWhileTransformation;
import de.uka.ilkd.key.speclang.LoopContract;
import de.uka.ilkd.key.speclang.LoopContractImpl;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;

/**
 * <p>
 * This rule transforms a block that starts with a for loop into one that starts with a while loop.
 * </p>
 *
 * <p>
 * This is necessary because the rules for loop contracts (subclasses of
 * {@link AbstractLoopContractRule}) can only be applied on blocks that start with a while loop.
 * </p>
 *
 * <p>
 * The transformation is equivalent to the {@link ForToWhileTransformation}, the only difference
 * being that we transform the whole block containing the loop instead of just the loop itself. This
 * is implemented as a built-in rule because the opening brace of the block on which it is applied
 * belongs to the non-active prefix and thus cannot be matched by the taclet language.
 * </p>
 *
 * <p>
 * Note that the actual transformation is performed in the constructor of {@link LoopContractImpl}.
 * </p>
 *
 * @author lanzinger
 */
public class LoopApplyHeadRule implements BuiltInRule {

    /**
     * The only instance of this class.
     */
    public static final LoopApplyHeadRule INSTANCE = new LoopApplyHeadRule();

    /**
     * The rule name.
     */
    public static final Name NAME = new Name("Loop Apply Head");

    @Nonnull
    @Override
    public ImmutableList<Goal> apply(Goal goal, Services services, RuleApp application)
            throws RuleAbortException {
        assert application instanceof LoopApplyHeadBuiltInRuleApp;
        LoopApplyHeadBuiltInRuleApp ruleApp = (LoopApplyHeadBuiltInRuleApp) application;

        ImmutableSet<LoopContract> contracts = ruleApp.contracts;
        LoopContract someContract = contracts.iterator().next();

        StatementBlock block = new StatementBlock(
            new While(someContract.getGuard(), someContract.getBody()), someContract.getTail());
        StatementBlock headAndBlock = new StatementBlock(someContract.getHead(), block);

        TermBuilder tb = services.getTermBuilder();
        AbstractLoopContractRule.Instantiation instantiation = ruleApp.instantiation;
        Modality modality = instantiation.modality;
        Term update = instantiation.update;
        Term target = instantiation.formula;

        JavaBlock newJavaBlock;
        newJavaBlock = JavaBlock.createJavaBlock(
            (StatementBlock) new ProgramElementReplacer(target.javaBlock().program(), services)
                    .replace(instantiation.statement, headAndBlock));

        for (LoopContract c : contracts) {
            LoopContract newContract = c.replaceEnhancedForVariables(block, services);

            services.getSpecificationRepository().removeLoopContract(c);
            services.getSpecificationRepository().addLoopContract(newContract, false);
            services.getSpecificationRepository()
                    .addBlockContract(c.toBlockContract().setBlock(headAndBlock));
        }

        Goal result = goal.split(1).head();
        result.changeFormula(
            new SequentFormula(tb.apply(update, tb.prog(modality, newJavaBlock, target.sub(0)))),
            ruleApp.pio);
        return ImmutableSLList.<Goal>nil().append(goal);
    }

    @Override
    public Name name() {
        return NAME;
    }

    @Override
    public String displayName() {
        return name().toString();
    }

    @Override
    public String toString() {
        return displayName();
    }

    @Override
    public IBuiltInRuleApp createApp(PosInOccurrence pos, TermServices services) {
        return new LoopApplyHeadBuiltInRuleApp(this, pos);
    }

    @Override
    public boolean isApplicable(Goal goal, PosInOccurrence pio) {
        if (pio == null || !pio.isTopLevel() || pio.isInAntec()) {
            return false;
        }

        // abort if inside of transformer
        if (Transformer.inTransformer(pio)) {
            return false;
        }

        final AbstractLoopContractRule.Instantiation instantiation =
            new AbstractLoopContractRule.Instantiator(pio.subTerm(), goal,
                goal.proof().getServices()).instantiate();

        if (instantiation == null) {
            return false;
        }

        final ImmutableSet<LoopContract> contracts = AbstractLoopContractRule
                .getApplicableContracts(instantiation, goal, goal.proof().getServices());

        for (LoopContract contract : contracts) {
            if (contract.getHead() != null) {
                return true;
            }
        }

        return false;
    }

    @Override
    public boolean isApplicableOnSubTerms() {
        return false;
    }

}
