/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.scripts;

import java.util.*;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.proof.*;
import de.uka.ilkd.key.rule.*;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.scripts.meta.*;

import org.key_project.logic.Name;
import org.key_project.logic.PosInTerm;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.prover.sequent.FormulaChangeInfo;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.sequent.SemisequentChangeInfo;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;

import org.checkerframework.checker.nullness.qual.MonotonicNonNull;
import org.jspecify.annotations.Nullable;

import static de.uka.ilkd.key.macros.ApplyScriptsMacro.USER_DATA_JML_OBTAIN_VAR_MAP;

/**
 * Command that applies a calculus rule All parameters are passed as strings and converted by the
 * command. The parameters are:
 * <ol>
 * <li>#2 = <String>rule name</String></li>
 * <li>on= key.core.logic.Term on which the rule should be applied to as String (find part of the
 * rule)</li>
 * <li>formula= toplevel formula in which term appears in</li>
 * <li>occ = occurrence number</li>
 * <li>inst_= instantiation</li>
 * </ol>
 */
public class ObtainCommand extends AbstractCommand {

    private static final Name INTRO_TACLET_NAME = new Name("intro");
    private static final Name ALL_RIGHT_TACLET_NAME = new Name("allRight");

    public ObtainCommand() {
        super(Parameters.class);
    }

    @Override
    public String getName() {
        return "__obtain";
    }

    @Override
    public void execute(ScriptCommandAst ast)
            throws ScriptException, InterruptedException {
        var args = state().getValueInjector().inject(new Parameters(), ast);

        var obtainMap = state().getUserData().get(USER_DATA_JML_OBTAIN_VAR_MAP);
        if (obtainMap == null) {
            throw new ScriptException(
                "No obtain variable map found. This command must be used within a JML proof.");
        }

        LocationVariable var = obtainMap.keySet().stream()
                .filter(lv -> lv.name().toString().equals(args.var))
                .findAny().orElseThrow(
                    () -> new ScriptException("No such obtain variable registered: " + args.var));

        JTerm skolem;
        if (args.equals != null) {
            skolem = executeEquals(var, args.equals);
        } else if (args.suchThat != null) {
            skolem = executeSuchThat(var, args.suchThat);
        } else if (args.fromGoal) {
            skolem = executeFromGoal(var);
        } else {
            throw new ScriptException(
                "Exactly one of 'such_that', 'equals', or 'from_goal' must be given.");
        }

        obtainMap.put(var, skolem.op(JFunction.class));

    }

    private JTerm executeFromGoal(LocationVariable var) throws ScriptException {
        Goal goal = state.getFirstOpenAutomaticGoal();

        // Pick the most recently changed succedent formula as the goal formula.
        var sci = goal.node().getNodeInfo().getSequentChangeInfo().getSemisequentChangeInfo(false);
        SequentFormula sequentFormula;
        if (!sci.addedFormulas().isEmpty()) {
            sequentFormula = sci.addedFormulas().get(0);
        } else if (!sci.modifiedFormulas().isEmpty()) {
            sequentFormula = sci.modifiedFormulas().get(0).newFormula();
        } else {
            // Fallback to last succedent if no change info is available
            sequentFormula = goal.node().sequent().succedent().getLast();
        }
        JTerm formula = (JTerm) sequentFormula.formula();
        while (formula.op() instanceof UpdateApplication) {
            formula = formula.sub(1);
        }
        if (formula.op() != Quantifier.ALL) {
            throw new ScriptException(
                "For 'obtain \\from_goal, the goal formula needs to be a universally quantified formula.");
        }

        Services services = state().getProof().getServices();
        Taclet intro = state.getProof().getEnv().getInitConfigForEnvironment()
                .lookupActiveTaclet(ALL_RIGHT_TACLET_NAME);
        TacletApp app = NoPosTacletApp.createNoPosTacletApp(intro);

        SchemaVariable sk = getSV(app.uninstantiatedVars(), "sk");
        String name =
            VariableNameProposer.DEFAULT.getNameProposal(var.name().toString(), services, null);
        app = app.createSkolemConstant(name, sk, var.sort(), true, goal);

        SchemaVariable b = getSV(app.uninstantiatedVars(), "b");
        app = app.addCheckedInstantiation(b, formula.sub(0), services, true);

        SchemaVariable u = getSV(app.uninstantiatedVars(), "u");
        app = app.addCheckedInstantiation(u,
            services.getTermBuilder().var((LogicVariable) formula.boundVars().get(0)), services,
            true);
        app = app.setPosInOccurrence(
            new PosInOccurrence(sequentFormula, PosInTerm.getTopLevel(), false), services);

        goal.apply(app);
        return app.instantiations().getInstantiation(sk);
    }

    private JTerm executeSuchThat(LocationVariable var, @Nullable JTerm suchThat)
            throws ScriptException {
        if (suchThat == null) {
            throw new ScriptException("'such_that' must not be null");
        }

        Services services = state().getProof().getServices();
        var tb = services.getTermBuilder();

        // 1) Replace program variable by a fresh logical variable in the condition.
        String base = var.name().toString();
        String lvName = VariableNameProposer.DEFAULT.getNameProposal(base, services, null);
        LogicVariable lv = new LogicVariable(new Name(lvName), var.sort());

        JTerm progVarTerm = tb.var(var);
        JTerm lvTerm = tb.var(lv);
        JTerm condWithLv = OpReplacer.replace(progVarTerm, lvTerm, suchThat,
            services.getTermFactory(), state().getProof());

        // 2) Ensure it is a formula
        JTerm asFormula = tb.convertToFormula(condWithLv);

        // 3) Existentially quantify and cut on it
        JTerm exFormula = tb.ex(lv, asFormula);

        Taclet cut = state.getProof().getEnv().getInitConfigForEnvironment()
                .lookupActiveTaclet(new Name("cut"));
        TacletApp cutApp = NoPosTacletApp.createNoPosTacletApp(cut);
        SchemaVariable cutSv = cutApp.uninstantiatedVars().iterator().next();
        cutApp = cutApp.addCheckedInstantiation(cutSv, exFormula, services, true);
        ImmutableList<Goal> goals = state.getFirstOpenAutomaticGoal().apply(cutApp);

        // 4) On the antecedent branch, apply exLeft to introduce a Skolem constant
        TermComparisonWithHoles cmp = new TermComparisonWithHoles(exFormula);
        Goal antecedentGoal = null;
        SequentFormula targetSf = null;
        for (Goal g : goals) {
            var matches = cmp.findTopLevelMatchesInSequent(g.node().sequent());
            for (var m : matches) {
                if (Boolean.TRUE.equals(m.first)) {
                    antecedentGoal = g;
                    targetSf = m.second;
                    break;
                }
            }
            if (antecedentGoal != null) break;
        }
        if (antecedentGoal == null || targetSf == null) {
            throw new ScriptException("Could not locate antecedent \\exists-formula after cut.");
        }

        FindTaclet exLeft = (FindTaclet) state.getProof().getEnv().getInitConfigForEnvironment()
                .lookupActiveTaclet(new Name("exLeft"));
        PosInOccurrence pio = new PosInOccurrence(targetSf, PosInTerm.getTopLevel(), true);
        MatchConditions mc = new MatchConditions();
        TacletApp exApp = PosTacletApp.createPosTacletApp(exLeft, mc, pio, services);

        var schemaVars = ImmutableSet.from(exLeft.collectSchemaVars());
        SchemaVariable u = getSV(schemaVars, "u");
        SchemaVariable b = getSV(schemaVars, "b");
        SchemaVariable sk = getSV(schemaVars, "sk");

        exApp = exApp.addInstantiation(u,
            services.getTermBuilder().tf().createTerm(targetSf.formula().boundVars().get(0)),
            true, services);
        exApp = exApp.addInstantiation(b, targetSf.formula().sub(0), true, services);

        String skName = VariableNameProposer.DEFAULT.getNameProposal(base, services, null);
        exApp = exApp.createSkolemConstant(skName, sk,
            targetSf.formula().boundVars().get(0).sort(), true, services);

        antecedentGoal.apply(exApp);
        return exApp.instantiations().getInstantiation(sk);
    }

    private JTerm executeEquals(LocationVariable var, @Nullable JTerm equals)
            throws ScriptException {
        Services services = state().getProof().getServices();
        Taclet intro = state.getProof().getEnv().getInitConfigForEnvironment()
                .lookupActiveTaclet(INTRO_TACLET_NAME);
        TacletApp app = NoPosTacletApp.createNoPosTacletApp(intro);
        SchemaVariable sk = getSV(app.uninstantiatedVars(), "sk");
        SchemaVariable t = getSV(app.uninstantiatedVars(), "t");
        String name =
            VariableNameProposer.DEFAULT.getNameProposal(var.name().toString(), services, null);
        app = app.createSkolemConstant(name, sk, var.sort(), true,
            state.getFirstOpenAutomaticGoal());
        app = app.addCheckedInstantiation(t, equals, services, true);
        state.getFirstOpenAutomaticGoal().apply(app);
        return app.instantiations().getInstantiation(sk);
    }

    private static SchemaVariable getSV(ImmutableSet<SchemaVariable> schemaVars, String name) {
        for (SchemaVariable schemaVar : schemaVars) {
            if (schemaVar.name().toString().equals(name)) {
                return schemaVar;
            }
        }
        throw new NoSuchElementException("No schema variable with name " + name);
    }

    @Documentation(category = "JML", value = """
            Command that introduces a fresh variable with a given name and sort.
            Exactly one of `such_that`, `equals`, or `from_goal` must be given.

            The command should not be called directly, but is used internally by
            the JML script support within KeY.
            """)
    public static class Parameters implements ValueInjector.VerifyableParameters {
        @Option(value = "var")
        @Documentation("Name of the variable to be instantiated.")
        public @MonotonicNonNull String var;

        @Option(value = "such_that")
        @Documentation("Condition that is to be established for the fresh variable.")
        public @Nullable JTerm suchThat;

        @Option(value = "from_goal")
        @Documentation("Top-level formula in which the term appears.")
        public @Nullable boolean fromGoal = false;

        @Option(value = "equals")
        @Documentation("Represented term for which this is an abbreviation.")
        public @Nullable JTerm equals;

        @Override
        public void verifyParameters() throws IllegalArgumentException, InjectionException {
            int cnt = 0;
            if (suchThat != null)
                cnt++;
            if (equals != null)
                cnt++;
            if (fromGoal)
                cnt++;
            if (cnt != 1) {
                throw new InjectionException(
                    "Exactly one of 'such_that', 'equals', or 'from_goal' must be given.");
            }
        }
    }

}
