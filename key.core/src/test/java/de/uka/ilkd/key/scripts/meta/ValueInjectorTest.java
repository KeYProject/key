/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.scripts.meta;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import de.uka.ilkd.key.scripts.AbstractCommand;
import de.uka.ilkd.key.scripts.ScriptCommandAst;

import org.assertj.core.api.Assertions;
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
            null);
        args.put("b", true);
        args.put("i", 42);

        assertThrows(ArgumentRequiredException.class, () -> {
            ValueInjector.injection(new PPCommand(), pp, ast);
        });

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
            null);
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

    @Test
    public void testFlag() throws ConversionException, ArgumentRequiredException,
            InjectionReflectionException, NoSpecifiedConverterException {
        class Options {
            @Flag
            boolean a;
            @Flag
            boolean b;
            @Flag
            boolean c = true;
        }
        var arg = new ScriptCommandAst("empty", Map.of("a", "true", "c", false), List.of("b"));
        var injector = ValueInjector.createDefault().inject(new Options(), arg);

        assertTrue(injector.a, "Field a should be true given as key-value argument");
        assertTrue(injector.b, "Field b should be true given as positional argument");
        assertFalse(injector.c, "Field c should be false, given explicitly as key-value argument");
    }


    @Test
    public void testVarargs() throws ConversionException, ArgumentRequiredException,
            InjectionReflectionException, NoSpecifiedConverterException {
        class Varargs {
            @OptionalVarargs(prefix = "a", as = Boolean.class)
            Map<String, Boolean> a;

            @OptionalVarargs(prefix = "b", as = Integer.class)
            Map<String, Integer> b;
        }
        var arg = new ScriptCommandAst("empty",
            Map.of("a1", "true", "b1", "1", "b2", "2", "a2", "false"),
            List.of());
        var values = ValueInjector.createDefault().inject(new Varargs(), arg);

        Assertions.assertThat(values.a)
                .containsEntry("a1", true)
                .containsEntry("a2", false);

        Assertions.assertThat(values.b)
                .containsEntry("b1", 1)
                .containsEntry("b2", 2);
    }



    public static class PP {
        @Option
        boolean b;

        @Option
        int i;

        @Option
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
