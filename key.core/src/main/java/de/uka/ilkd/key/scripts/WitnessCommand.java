/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */

package de.uka.ilkd.key.scripts;

import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.Quantifier;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.RuleAppIndex;
import de.uka.ilkd.key.rule.*;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import org.key_project.logic.Name;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import java.util.NoSuchElementException;
import java.util.Set;
import java.util.regex.Pattern;

/**
 * witness "\exists int x; phi(x)" as="x_12"
 * <p>
 * witness "\forall int x; phi(x)" as="x_13"
 * <p>
 * witness "\exists int x; phi(x)" as="x_14" cut=true
 *
 * Possibly with an assertion before to make sure that the formula is on the sequent.
 *
 * @author mulbrich
 */
public class WitnessCommand extends AbstractCommand {

    private static final Pattern GOOD_NAME = Pattern.compile("[a-zA-Z][a-zA-Z0-9_]*");
    private static final Name ANTEC_TACLET = new Name("exLeft");
    private static final Name SUCC_TACLET = new Name("allRight");

    public WitnessCommand() {
        super(Parameters.class);
    }

    @Override
    public String getName() {
        return "witness";
    }

    @Override
    public void execute(ScriptCommandAst ast) throws ScriptException, InterruptedException {

        Parameters params = state().getValueInjector().inject(new Parameters(), ast);

        Goal goal = state.getFirstOpenAutomaticGoal();
        Services services = state.getProof().getServices();

        TermComparisonWithHoles tc = new TermComparisonWithHoles(services);
        Pair<Boolean, SequentFormula> match = goal.node().sequent().antecedent().asList().stream()
                .filter(f -> tc.compareModHoles(params.formula, f.formula()))
                .map(f -> new Pair<>(true, f))
                .findFirst().orElse(
                        goal.node().sequent().succedent().asList().stream()
                                .filter(f -> tc.compareModHoles(params.formula, f.formula()))
                                .map(f -> new Pair<>(false, f))
                                .findFirst().orElse(null)
                );

        if (match == null) {
            throw new ScriptException("Cannot match the formula argument");
        }

        Operator op = match.second.formula().op();
        Operator expected = match.first ? Quantifier.EX : Quantifier.ALL;
        if (op != expected) {
            throw new ScriptException("Expected quantifier " + expected + ", but got " + op);
        }

        if(!GOOD_NAME.matcher(params.as).matches()) {
            throw new ScriptException("Invalid name: " + params.as);
        }

        Name tacletName = match.first ? ANTEC_TACLET : SUCC_TACLET;
        FindTaclet taclet = (FindTaclet) state.getProof().getEnv().getInitConfigForEnvironment()
                .lookupActiveTaclet(tacletName);
        PosInOccurrence pio = new PosInOccurrence(match.second, PosInTerm.getTopLevel(), match.first);
        MatchConditions mc = new MatchConditions();
        TacletApp app = PosTacletApp.createPosTacletApp(taclet, mc, pio, services);
        Set<SchemaVariable> schemaVars = taclet.collectSchemaVars();
        app = app.addInstantiation(getSV(schemaVars, "u"),
                services.getTermBuilder().tf().createTerm(match.second.formula().boundVars().get(0)),
                true, services);
        app = app.addInstantiation(getSV(schemaVars, "b"), match.second.formula().sub(0), true, services);
        app = app.createSkolemConstant(params.as, getSV(schemaVars, "sk"), true, services);

        Goal g = state.getFirstOpenAutomaticGoal();
        g.apply(app);
    }

    private static SchemaVariable getSV(Set<SchemaVariable> schemaVars, String name) {
        for (SchemaVariable schemaVar : schemaVars) {
            if(schemaVar.name().toString().equals(name)) {
                return schemaVar;
            }
        }
        throw new NoSuchElementException("No schema variable with name " + name);
    }

    public static class Parameters {
        @Option(value = "as")
        public String as;
        @Option(value = "#2")
        public Term formula;
    }

}
