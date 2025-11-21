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

import org.key_project.prover.sequent.Sequent;

import org.checkerframework.checker.nullness.qual.MonotonicNonNull;

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

    public static class Parameters {
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
