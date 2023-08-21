/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.macros.scripts;

import java.util.Map;
import javax.script.ScriptContext;
import javax.script.ScriptEngine;
import javax.script.ScriptEngineManager;

import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.macros.scripts.meta.Option;
import de.uka.ilkd.key.macros.scripts.meta.ValueInjector;
import de.uka.ilkd.key.parser.ParserException;
import de.uka.ilkd.key.pp.AbbrevException;
import de.uka.ilkd.key.proof.Proof;

public class JavascriptCommand extends AbstractCommand<JavascriptCommand.Parameters> {

    private static final String PREAMBLE = "var goal = __state.getSelectedGoal();\n"
        + "function setVar(v, t) { __state.setVar(v,t); }\n";

    public JavascriptCommand() {
        super(Parameters.class);
    }

    @Override
    public void execute(Parameters args) throws ScriptException, InterruptedException {
        ScriptEngineManager factory = new ScriptEngineManager();
        // create JavaScript engine
        ScriptEngine engine = factory.getEngineByName("JavaScript");
        // evaluate JavaScript code from given file - specified by first argument
        JavascriptInterface jsIntf = new JavascriptInterface(proof, state);

        engine.getBindings(ScriptContext.GLOBAL_SCOPE).put("__state", jsIntf);
        try {
            engine.eval(PREAMBLE);
            engine.eval(args.script);
        } catch (javax.script.ScriptException e) {
            throw new ScriptException(e);
        }
    }

    @Override
    public Parameters evaluateArguments(EngineState state, Map<String, String> arguments)
            throws Exception {
        return ValueInjector.injection(this, new Parameters(), arguments);
    }

    @Override
    public String getName() {
        return "javascript";
    }

    public static class Parameters {
        @Option("#2")
        public String script;
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

        public void setVar(String var, Term term) throws ScriptException {

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
