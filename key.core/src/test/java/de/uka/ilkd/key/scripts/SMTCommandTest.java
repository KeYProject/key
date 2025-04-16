/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.scripts;

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
        HashMap<String, Object> args = new HashMap<>();
        args.put("solver", "z3");

        SMTCommand cmd = new SMTCommand();
        SMTCommand.SMTCommandArguments o = cmd.evaluateArguments(new EngineState(null, null), args);
        Assertions.assertEquals("z3", o.solver);
    }
}
