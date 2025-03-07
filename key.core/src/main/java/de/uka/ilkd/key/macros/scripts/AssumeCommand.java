/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.macros.scripts;

import java.util.Map;

import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.FormulaSV;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.SchemaVariableFactory;
import de.uka.ilkd.key.macros.scripts.meta.Documentation;
import de.uka.ilkd.key.macros.scripts.meta.Option;
import de.uka.ilkd.key.rule.*;

import de.uka.ilkd.key.rule.tacletbuilder.TacletGoalTemplate;
import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import org.key_project.logic.Name;
import org.key_project.util.collection.DefaultImmutableMap;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;

/**
 * The assume statement for proof debugging purposes
 *
 *  See exported documentation at @{@link FormulaParameter} at the end of this file.
 */
@NullMarked
public class AssumeCommand extends AbstractCommand<AssumeCommand.FormulaParameter> {
    private static final Name TACLET_NAME = new Name("UNSOUND_ASSUME");

    /**
     * The taclet that is used to implement the assume command.
     *
     * The taclet UNSOUND_ASSUME { \add( b ==> ) } is obviously unsound, but it is used for debugging
     * purposes. It is constructed programmatically here, because it should not show up in the sources
     * of the key repository.
     *
     * (Earlier versions had the unsound axion taclet amongst the axioms in KeY and special-cased around it.)
     */
    private static final Taclet ASSUME_TACLET;

    static {
        TacletApplPart applPart = new TacletApplPart(Sequent.EMPTY_SEQUENT, ImmutableList.of(), ImmutableList.of(), ImmutableList.of(), ImmutableList.of());
        FormulaSV sv = SchemaVariableFactory.createFormulaSV(new Name("b"));
        Term b = new TermFactory().createTerm(sv);
        TacletGoalTemplate goal = new TacletGoalTemplate(
                Sequent.createAnteSequent(new Semisequent(ImmutableList.of(new SequentFormula(b)))),
                            ImmutableList.of());
        ASSUME_TACLET = new NoFindTaclet(TACLET_NAME, applPart, ImmutableList.of(goal), ImmutableList.of(), new TacletAttributes(),
                DefaultImmutableMap.nilMap(), ChoiceExpr.TRUE, ImmutableSet.empty());
    }

    public AssumeCommand() {
        super(FormulaParameter.class);
    }

    @Override
    public FormulaParameter evaluateArguments(EngineState state,
            Map<String, Object> arguments)
            throws Exception {
        return state.getValueInjector().inject(this, new FormulaParameter(), arguments);
    }

    @Override
    public String getName() {
        return "assume";
    }

    @Override
    public void execute(FormulaParameter parameter) throws ScriptException, InterruptedException {
        TacletApp app = NoPosTacletApp.createNoPosTacletApp(ASSUME_TACLET);
        SchemaVariable sv = app.uninstantiatedVars().iterator().next();

        app = app.addCheckedInstantiation(sv, parameter.formula, state.getProof().getServices(),
            true);
        state.getFirstOpenAutomaticGoal().apply(app);
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
