/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.macros.scripts.meta;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.macros.scripts.AbstractCommand;
import de.uka.ilkd.key.macros.scripts.EngineState;
import de.uka.ilkd.key.macros.scripts.ScriptException;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

/**
 * @author Alexander Weigl
 * @version 1 (02.05.17)
 */
public class ValueInjectorTest {
    @Test
    public void testInjectionSimple() throws Exception {
        PP pp = new PP();
        Map<String, String> args = new HashMap<>();
        args.put("b", "true");
        args.put("i", "42");
        args.put("s", "blubb");

        ValueInjector.injection(null, pp, args);

        assertTrue(pp.b);
        assertEquals(42, pp.i);
        assertEquals("blubb", pp.s);

    }

    @Test
    public void testRequired() {
        PP pp = new PP();
        Map<String, String> args = new HashMap<>();
        args.put("b", "true");
        args.put("s", "blubb");
        assertThrows(ArgumentRequiredException.class,
            () -> ValueInjector.injection(new PPCommand(), pp, args));
    }

    @Test
    public void testInferScriptArguments() throws NoSuchFieldException {
        List<ProofScriptArgument<PP>> meta = ArgumentsLifter.inferScriptArguments(PP.class, null);
        assertEquals(3, meta.size());

        {
            ProofScriptArgument<PP> b = meta.get(0);
            assertEquals("b", b.getName());
            assertEquals(PP.class.getDeclaredField("b"), b.getField());
            assertEquals(Boolean.TYPE, b.getType());
            assertTrue(b.isRequired());
        }

        {
            ProofScriptArgument<PP> i = meta.get(1);
            assertEquals("i", i.getName());
            assertEquals(PP.class.getDeclaredField("i"), i.getField());
            assertEquals(Integer.TYPE, i.getType());
            assertTrue(i.isRequired());
        }

        {
            ProofScriptArgument<PP> i = meta.get(2);
            assertEquals("s", i.getName());
            assertEquals(PP.class.getDeclaredField("s"), i.getField());
            assertEquals(String.class, i.getType());
            assertFalse(i.isRequired());
        }

    }

    public static class PP {
        @Option("b")
        boolean b;
        @Option(value = "i", required = true)
        int i;
        @Option(value = "s", required = false)
        String s;
    }

    private static class PPCommand extends AbstractCommand<PP> {
        public PPCommand() {
            super(null);
        }

        @Override
        public PP evaluateArguments(EngineState state, Map<String, String> arguments) {
            return null;
        }

        @Override
        public void execute(AbstractUserInterfaceControl uiControl, PP args, EngineState stateMap)
                throws ScriptException, InterruptedException {
        }

        @Override
        public String getName() {
            return "pp";
        }
    }
}
