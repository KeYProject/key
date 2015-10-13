package de.uka.ilkd.key.macros.scripts;

import java.util.Map;

import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.SchemaVariableFactory;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.parser.ParserException;
import de.uka.ilkd.key.pp.AbbrevException;
import de.uka.ilkd.key.pp.AbbrevMap;
import de.uka.ilkd.key.proof.Proof;

public class SchemaVarCommand extends AbstractCommand {

    @Override
    public void execute(AbstractUserInterfaceControl uiControl, Proof proof,
            Map<String, String> args, Map<String, Object> stateMap)
            throws ScriptException, InterruptedException {
        String type = args.get("#2");
        String var = args.get("#3");

        if(type == null || var == null) {
            throw new ScriptException("Missing argument: type var");
        }

        AbbrevMap abbrMap = (AbbrevMap)stateMap.get(ABBREV_KEY);
        if(abbrMap == null) {
            abbrMap = new AbbrevMap();
            stateMap.put(ABBREV_KEY, abbrMap);
        }

        if(!var.matches("@[a-zA-Z0-9_]")) {
            throw new ScriptException("Illegal variable name: " + var);
        }

        var = var.substring(1);

        try {
            SchemaVariable sv;
            if("Formula".equals(type)) {
                sv = SchemaVariableFactory.createFormulaSV(new Name("_SCHEMA_" + var));
            } else {
                Sort sort = toSort(proof, stateMap, type);
                sv = SchemaVariableFactory.createTermSV(new Name("_SCHEMA_" + var), sort);
            }

            Term term = proof.getServices().getTermFactory().createTerm(sv);

            abbrMap.put(term, var, true);
        } catch (Exception e) {
            throw new ScriptException(e);
        }

    }

    @Override
    public String getName() {
        return "schemaVar";
    }

}
