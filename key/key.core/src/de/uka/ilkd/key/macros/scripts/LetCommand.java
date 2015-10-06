package de.uka.ilkd.key.macros.scripts;

import java.util.Map;

import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.parser.ParserException;
import de.uka.ilkd.key.pp.AbbrevMap;
import de.uka.ilkd.key.proof.Proof;

public class LetCommand extends AbstractCommand {

    @Override
    public void execute(AbstractUserInterfaceControl uiControl, Proof proof,
            Map<String, String> args, Map<String, Object> stateMap)
            throws ScriptException, InterruptedException {

        for (Map.Entry<String, String> entry : args.entrySet()) {

            AbbrevMap abbrMap = (AbbrevMap)stateMap.get(ABBREV_KEY);
            if(abbrMap == null) {
                abbrMap = new AbbrevMap();
                stateMap.put(ABBREV_KEY, abbrMap);
            }

            String key = entry.getKey();
            if("#1".equals(key)) {
                continue;
            }
            if("#literal".equals(key)) {
                continue;
            }
            if(!key.startsWith("@")) {
                throw new ScriptException("Unexpected parameter to let, only @var allowed: " + key);
            }

            // get rid of @
            key = key.substring(1);

            if(abbrMap.containsAbbreviation(key)) {
                // XXX desired or not?
                throw new ScriptException(key + " is already fixed in this script");
            }
            try {
                abbrMap.put(toTerm(proof, stateMap, entry.getValue(), null), key, true);
            } catch (Exception e) {
                throw new ScriptException(e);
            }
        }

    }

    @Override
    public String getName() {
        return "let";
    }

}
