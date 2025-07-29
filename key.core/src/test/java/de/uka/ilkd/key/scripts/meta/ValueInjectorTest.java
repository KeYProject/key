/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.scripts.meta;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.scripts.AbstractCommand;
import de.uka.ilkd.key.scripts.EngineState;
import de.uka.ilkd.key.scripts.ScriptCommandAst;

import org.checkerframework.checker.nullness.qual.MonotonicNonNull;
import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
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
        Map<String, Object> args = new HashMap<>();
        ScriptCommandAst ast = new ScriptCommandAst("pp", args, new LinkedList<>(),
            null, null);
        args.put("b", true);
        args.put("i", 42);
        args.put("q", "blubb");

        ValueInjector.injection(new PPCommand(), pp, ast);

        assertTrue(pp.b);
        assertEquals(42, pp.i);
        assertEquals("blubb", pp.required);

    }

    @Test
    public void testRequired() {
        PP pp = new PP();
        Map<String, Object> args = new HashMap<>();
        ScriptCommandAst ast = new ScriptCommandAst("pp", args, new LinkedList<>(),
            null, null);
        args.put("b", "true");
        args.put("s", "blubb");
        assertThrows(ArgumentRequiredException.class,
            () -> ValueInjector.injection(new PPCommand(), pp, ast));
    }

    @Test
    public void testInferScriptArguments() throws NoSuchFieldException {
        List<ProofScriptArgument> meta = ArgumentsLifter.inferScriptArguments(PP.class);
        assertEquals(4, meta.size());

        {
            ProofScriptArgument b = meta.getFirst();
            assertEquals("b", b.getName());
            assertEquals(PP.class.getDeclaredField("b"), b.getField());
            assertEquals(Boolean.TYPE, b.getType());
            assertTrue(b.isRequired());
        }

        {
            ProofScriptArgument i = meta.get(1);
            assertEquals("i", i.getName());
            assertEquals(PP.class.getDeclaredField("i"), i.getField());
            assertEquals(Integer.TYPE, i.getType());
            assertTrue(i.isRequired());
        }

        {
            ProofScriptArgument i = meta.get(2);
            assertEquals("s", i.getName());
            assertEquals(PP.class.getDeclaredField("s"), i.getField());
            assertEquals(String.class, i.getType());
            assertFalse(i.isRequired());
        }

    }

    public static class PP {
        @Option("b")
        boolean b;

        @Option(value = "i")
        int i;

        @Option(value = "s")
        @Nullable
        String s;

        @Option("q")
        @MonotonicNonNull
        String required;
    }

    @NullMarked
    private static class PPCommand extends AbstractCommand {
        public PPCommand() {
            super(null);
        }

        @Override
        public void execute(ScriptCommandAst args) {

        }

        @Override
        public String getName() {
            return "pp";
        }
    }
}
