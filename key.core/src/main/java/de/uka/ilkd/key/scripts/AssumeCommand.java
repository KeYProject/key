/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.scripts;


import de.uka.ilkd.key.logic.ChoiceExpr;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.FormulaSV;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.SchemaVariableFactory;
import de.uka.ilkd.key.rule.*;
import de.uka.ilkd.key.rule.tacletbuilder.TacletGoalTemplate;
import de.uka.ilkd.key.scripts.meta.Documentation;
import de.uka.ilkd.key.scripts.meta.Option;
import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import org.key_project.logic.Name;
import org.key_project.util.collection.DefaultImmutableMap;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;

/**
 * The assume statement for proof debugging purposes
 * <p>
 * See exported documentation at @{@link FormulaParameter} at the end of this file.
 */
@NullMarked
public class AssumeCommand extends AbstractCommand {
    private static final Name TACLET_NAME = new Name("UNSOUND_ASSUME");

    /**
     * The taclet that is used to implement the assume command.
     * <p>
     * The taclet UNSOUND_ASSUME { \add( b ==> ) } is obviously unsound, but it is used for
     * debugging
     * purposes. It is constructed programmatically here, because it should not show up in the
     * sources
     * of the key repository.
     * <p>
     * (Earlier versions had the unsound axion taclet amongst the axioms in KeY and special-cased
     * around it.)
     */
    private static @Nullable Taclet assumeTaclet;

    public AssumeCommand() {
        super(FormulaParameter.class);
    }

    private static @NonNull Taclet createAssumeTaclet() {
        if (assumeTaclet == null) {
            TacletApplPart applPart = new TacletApplPart(Sequent.EMPTY_SEQUENT, ImmutableList.of(),
                ImmutableList.of(), ImmutableList.of(), ImmutableList.of());
            FormulaSV sv = SchemaVariableFactory.createFormulaSV(new Name("b"));
            Term b = new TermFactory().createTerm(sv);
            TacletGoalTemplate goal = new TacletGoalTemplate(
                Sequent.createAnteSequent(new Semisequent(ImmutableList.of(new SequentFormula(b)))),
                ImmutableList.of());
            assumeTaclet = new NoFindTaclet(TACLET_NAME, applPart, ImmutableList.of(goal),
                ImmutableList.of(), new TacletAttributes(),
                DefaultImmutableMap.nilMap(), ChoiceExpr.TRUE, ImmutableSet.empty());
        }
        return assumeTaclet;
    }

    @Override
    public String getName() {
        return "assume";
    }

    public void execute(ScriptCommandAst arguments) throws ScriptException, InterruptedException {
        var parameter = state().getValueInjector()
                .inject(this, new FormulaParameter(), arguments);
        Taclet cut =
            state().getProof().getEnv().getInitConfigForEnvironment()
                    .lookupActiveTaclet(TACLET_NAME);
        TacletApp app = NoPosTacletApp.createNoPosTacletApp(cut);
        SchemaVariable sv = app.uninstantiatedVars().iterator().next();

        app = app.addCheckedInstantiation(sv, parameter.formula, state().getProof().getServices(),
            true);
        state().getFirstOpenAutomaticGoal().apply(app);
    }

    @Documentation("""
            The assume command is an unsound debug command. It takes one argument, a formula,
            that is added to the antecedent of the current goal. The command is implemented
            using a local unsound taclet, UNSOUND_ASSUME.""")
    public static class FormulaParameter {
        @Option(value = "#2", help = "The formula to be assumed.")
        public Term formula;
    }
}
