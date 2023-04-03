package de.uka.ilkd.key.macros.scripts;

import java.util.HashMap;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;

/**
 * @author Alexander Weigl
 * @version 1 (17.10.19)
 */
public class SMTCommandTest {
    @Test
    public void testInstantiation() throws Exception {
        HashMap<String, String> args = new HashMap<>();
        args.put("solver", "z3");

        SMTCommand cmd = new SMTCommand();
        SMTCommand.SMTCommandArguments o = cmd.evaluateArguments(new EngineState(null), args);
        Assertions.assertEquals("z3", o.solver);
    }
}
