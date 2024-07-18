/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */

package de.uka.ilkd.key.scripts;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.Quantifier;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.*;
import de.uka.ilkd.key.scripts.meta.Argument;
import de.uka.ilkd.key.scripts.meta.Documentation;
import de.uka.ilkd.key.scripts.meta.Option;
import org.checkerframework.checker.nullness.qual.MonotonicNonNull;
import org.key_project.logic.Name;
import org.key_project.logic.PosInTerm;
import org.key_project.logic.op.Operator;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.util.collection.Pair;

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

        TermComparisonWithHoles comp = params.formula.getMatcher();

        // First component: true for antecedent, false for succedent
        Pair<Boolean, SequentFormula> match = comp.findUniqueToplevelMatchInSequent(goal.node().sequent());
        if (match == null) {
            throw new ScriptException("Cannot unique match the formula argument");
        }

        Operator op = match.second.formula().op();
        Operator expected = match.first ? Quantifier.EX : Quantifier.ALL;
        if (op != expected) {
            throw new ScriptException("Expected quantifier " + expected + ", but got " + op);
        }

        if(!GOOD_NAME.matcher(params.as).matches()) {
            throw new ScriptException("Invalid name: " + params.as);
        }

        NamespaceSet nss = services.getNamespaces();
        Name asName = new Name(params.as);
        if(nss.functions().lookup(asName) != null) {
            throw new ScriptException("Name already used as function or predicate: " + params.as);
        }
        if(nss.programVariables().lookup(asName) != null) {
            throw new ScriptException("Name already used as program variable: " + params.as);
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
        app = app.createSkolemConstant(params.as, getSV(schemaVars, "sk"), match.second.formula().boundVars().get(0).sort(), true, services);

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

    @Documentation(category = "Fundamental", value = """
            Provides a witness symbol for an existential or universal quantifier.
            The given formula must be present on the sequent. Placeholders are allowed.
            The command fails if the formula cannot be uniquely matched on the sequent.
            The witness symbol `as` must be a valid identifier and not already used as function, predicate, or
            program variable name. The new function symbol is created as a Skolem constant.
            
            #### Example:
            
            If the sequent contains the formula `\\exists int x; x > 0` in the antecedent then the command
            `witness "\\exists int x; x > 0" as="x_12"` will introduce the witness symbol `x_12` for which "x_12 > 0`
            holds and is added to the antecedent.
            """)
    public static class Parameters {
        @Documentation("The name of the witness symbol to be created.")
        @Option(value = "as")
        public @MonotonicNonNull String as;

        @Documentation("The formula containing the quantifier for which a witness should be provided. Placeholders are allowed.")
        @Argument
        public @MonotonicNonNull TermWithHoles formula;
    }

}
