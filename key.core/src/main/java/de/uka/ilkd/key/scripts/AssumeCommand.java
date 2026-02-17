/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.scripts;

import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.SchemaVariableFactory;
import de.uka.ilkd.key.proof.calculus.JavaDLSequentKit;
import de.uka.ilkd.key.rule.NoFindTaclet;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.tacletbuilder.TacletGoalTemplate;
import de.uka.ilkd.key.scripts.meta.Argument;
import de.uka.ilkd.key.scripts.meta.Documentation;

import org.key_project.logic.ChoiceExpr;
import org.key_project.logic.Name;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.prover.rules.ApplicationRestriction;
import org.key_project.prover.rules.TacletApplPart;
import org.key_project.prover.rules.TacletAttributes;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.util.collection.DefaultImmutableMap;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;

import org.checkerframework.checker.nullness.qual.MonotonicNonNull;
import org.jspecify.annotations.NullMarked;

/**
 * The assume statement for proof debugging purposes
 * <p>
 * See exported documentation at @{@link FormulaParameter} at the end of this file.
 */
@NullMarked
public class AssumeCommand extends AbstractCommand {

    /**
     * The taclet for the assume command is a local constructed taclet that is not available in the
     * usual
     * KeY taclet base. This is on purpose. Proofs can be conducted and saved with this command,
     * but they cannot be reloaded.
     */
    private static final Taclet ASSUME_TACLET;

    static {
        SchemaVariable sv = SchemaVariableFactory.createFormulaSV(new Name("condition"));
        JavaDLSequentKit kit = JavaDLSequentKit.getInstance();
        TacletApplPart applPart =
            new TacletApplPart(kit.getEmptySequent(),
                new ApplicationRestriction(ApplicationRestriction.IN_SEQUENT_STATE),
                ImmutableList.of(),
                ImmutableList.of(), ImmutableList.of(), ImmutableList.of());
        SequentFormula sf = new SequentFormula(new TermFactory().createTerm(sv));
        TacletGoalTemplate goal = new TacletGoalTemplate(kit.newAntecedent(ImmutableList.of(sf)),
            ImmutableList.of(), ImmutableSet.of());
        ASSUME_TACLET =
            new NoFindTaclet(new Name("CHEAT_ASSUME"), applPart, ImmutableList.of(goal),
                ImmutableList.of(),
                new TacletAttributes("assume", null), DefaultImmutableMap.nilMap(), ChoiceExpr.TRUE,
                ImmutableSet.empty());
    }

    public AssumeCommand() {
        super(FormulaParameter.class);
    }

    @Override
    public String getName() {
        return "assume";
    }

    public void execute(ScriptCommandAst arguments) throws ScriptException, InterruptedException {
        var parameter = state().getValueInjector()
                .inject(new FormulaParameter(), arguments);
        TacletApp app = NoPosTacletApp.createNoPosTacletApp(ASSUME_TACLET);
        SchemaVariable sv = app.uninstantiatedVars().iterator().next();

        app = app.addCheckedInstantiation(sv, parameter.formula, state.getProof().getServices(),
            true);
        state.getFirstOpenAutomaticGoal().apply(app);
    }

    @Documentation(category = "Control",
        value = """
                The assume command is an **unsound** taclet rule and adds a formula to the antecedent of the current goal
                Can be used for debug and proof exploration purposes. Proof files for proofs with this command cannot
                be reloaded.
                """)
    public static class FormulaParameter {
        @Argument
        @Documentation("The formula to be assumed.")
        public @MonotonicNonNull JTerm formula;
    }
}
