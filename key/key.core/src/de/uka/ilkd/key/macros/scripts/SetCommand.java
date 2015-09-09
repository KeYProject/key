package de.uka.ilkd.key.macros.scripts;

import java.util.Map;
import java.util.Properties;

import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.proof.Proof;

public class SetCommand extends AbstractCommand {

    @Override
    public void execute(AbstractUserInterfaceControl uiControl, Proof proof,
            Map<String, String> args) throws ScriptException,
            InterruptedException {

        if(!args.containsKey("key")) {
            throw new ScriptException("set needs a key");
        }

        if(!args.containsKey("value")) {
            throw new ScriptException("set needs a value");
        }

        String key = args.get("key");
        String value = args.get("value");
        Properties p = new Properties();
        p.put(key, value);

        proof.getSettings().update(p);
    }

    @Override
    public String getName() {
        return "set";
    }

}
