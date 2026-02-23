/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.scripts;

import javax.script.ScriptContext;
import javax.script.ScriptEngine;
import javax.script.ScriptEngineManager;

import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.parser.ParserException;
import de.uka.ilkd.key.pp.AbbrevException;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.scripts.meta.Argument;
import de.uka.ilkd.key.scripts.meta.Documentation;

import org.key_project.prover.sequent.Sequent;

import org.checkerframework.checker.nullness.qual.MonotonicNonNull;

/**
 * This command allows to execute arbitrary JavaScript code. The code is executed in a context where
 * the current selected goal is available as {@code goal} and a function {@code setVar(v,t)} is
 * available to set an abbreviation (where {@code v} is the name of the variable including the
 * leading {@code @} and {@code t} is either a term or a string that can be parsed as a term).
 * <p>
 * Example:
 *
 * <pre>
 * javascript {
 *   var x = goal.getAntecedent().get(0).getFormula();
 *   setVar("@myVar", x);
 * }
 * </pre>
 *
 * This command is powerful but should be used with care, as it can easily lead to unsound proofs if
 * used incorrectly.
 */
public class JavascriptCommand extends AbstractCommand {

    private static final String PREAMBLE = """
            var goal = __state.getSelectedGoal();
            function setVar(v, t) { __state.setVar(v,t); }
            """;

    public JavascriptCommand() {
        super(Parameters.class);
    }

    @Override
    public void execute(ScriptCommandAst params) throws ScriptException, InterruptedException {
        var args = state().getValueInjector().inject(new Parameters(), params);

        ScriptEngineManager factory = new ScriptEngineManager();
        // create JavaScript engine
        ScriptEngine engine = factory.getEngineByName("JavaScript");
        // evaluate JavaScript code from given file - specified by first argument
        JavascriptInterface jsIntf = new JavascriptInterface(proof, state());

        engine.getBindings(ScriptContext.GLOBAL_SCOPE).put("__state", jsIntf);
        try {
            engine.eval(PREAMBLE);
            engine.eval(args.script);
        } catch (javax.script.ScriptException e) {
            throw new ScriptException(e);
        }
    }

    @Override
    public String getName() {
        return "javascript";
    }

    @Documentation(category = "Internal",
        value = """
                This command allows to execute arbitrary JavaScript code. The code is executed in a context where
                the current selected goal is available as `goal` and a function `setVar(v,t)` is
                available to set an abbreviation (where `v` is the name of the variable including the
                leading `@` and `t` is either a term or a string that can be parsed as a term).

                #### Example:
                ```
                javascript {
                  var x = goal.getAntecedent().get(0).getFormula();
                  setVar("@myVar", x);
                }
                ```

                This command is powerful but should be used with care, as it can easily lead to unsound proofs if
                used incorrectly.
                """)
    public static class Parameters {
        @Documentation("The JavaScript code to execute.")
        @Argument
        public @MonotonicNonNull String script;
    }

    public static class JavascriptInterface {
        private final EngineState state;

        public JavascriptInterface(Proof proof, EngineState state) {
            this.state = state;
        }

        public int arg() {
            return 0;
        }

        public Sequent getSelectedGoal() throws ScriptException {
            return state.getFirstOpenAutomaticGoal().sequent();
        }

        public void setVar(String var, JTerm term) throws ScriptException {

            if (!var.matches("@[a-zA-Z0-9_]")) {
                throw new ScriptException("Is not a variable name: " + var);
            }

            var = var.substring(1);
            try {
                state.getAbbreviations().put(term, var, true);
            } catch (AbbrevException e) {
                throw new ScriptException();
            }
        }

        public void setVar(String var, String term) throws ScriptException {
            try {
                setVar(var, state.toTerm(term, null));
            } catch (ParserException e) {
                throw new ScriptException(e);
            }
        }

    }

}
