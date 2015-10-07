package de.uka.ilkd.key.macros.scripts;

import java.util.Map;

import javax.script.ScriptContext;
import javax.script.ScriptEngine;
import javax.script.ScriptEngineManager;

import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.parser.ParserException;
import de.uka.ilkd.key.pp.AbbrevException;
import de.uka.ilkd.key.pp.AbbrevMap;
import de.uka.ilkd.key.proof.Proof;

public class JavascriptCommand extends AbstractCommand {

    public static class JavascriptInterface {
        private final Proof proof;
        private final Map<String, Object> state;

        public JavascriptInterface(Proof proof, Map<String, Object> state) {
            this.proof = proof;
            this.state = state;
        }

        public int arg() { return 0; }

        public Sequent getSelectedGoal() throws ScriptException {
            return getFirstOpenGoal(proof, state).sequent();
        }

        public void setVar(String var, Term term) throws ScriptException {

            if(!var.matches("@[a-zA-Z0-9_]") ) {
                throw new ScriptException("Is not a variable name: " +var);
            }

            var = var.substring(1);

            AbbrevMap abbrMap = (AbbrevMap)state.get(ABBREV_KEY);
            if(abbrMap == null) {
                abbrMap = new AbbrevMap();
                state.put(ABBREV_KEY, abbrMap);
            }
            try {
                abbrMap.put(term, var, true);
            } catch (AbbrevException e) {
                throw new ScriptException();
            }
        }

        public void setVar(String var, String term) throws ScriptException {
            try {
                setVar(var, toTerm(proof, state, term, null));
            } catch (ParserException e) {
                throw new ScriptException(e);
            }
        }

    }

    private static final String PREAMBLE =
            "var goal = __state.getSelectedGoal();\n" +
            "function setVar(v, t) { __state.setVar(v,t); }\n";

    @Override
    public void execute(AbstractUserInterfaceControl uiControl, Proof proof,
            Map<String, String> args, Map<String, Object> stateMap)
            throws ScriptException, InterruptedException {

        String script = args.get("#2");

        ScriptEngineManager factory = new ScriptEngineManager();
        // create JavaScript engine
        ScriptEngine engine = factory.getEngineByName("JavaScript");
        // evaluate JavaScript code from given file - specified by first argument
        JavascriptInterface jsIntf = new JavascriptInterface(proof, stateMap);

        engine.getBindings(ScriptContext.GLOBAL_SCOPE).put("__state", jsIntf);
        try {
            engine.eval(PREAMBLE);
            engine.eval(script);
        } catch (javax.script.ScriptException e) {
            throw new ScriptException(e);
        }
    }

    @Override
    public String getName() {
        return "javascript";
    }

}
