/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.nparser;

import java.io.*;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.*;
import java.util.stream.Stream;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.logic.sort.GenericSort;
import de.uka.ilkd.key.logic.sort.ParametricSortInstance;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.proof.io.ProblemLoaderControl;
import de.uka.ilkd.key.proof.io.SingleThreadProblemLoader;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.UninstantiatedGenericSortCollector;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.util.HelperClassForTests;

import org.key_project.logic.ChoiceExpr;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.logic.sort.Sort;
import org.key_project.prover.rules.conditions.NewDependingOn;
import org.key_project.prover.rules.conditions.NewVarcond;
import org.key_project.prover.rules.conditions.NotFreeIn;

import org.jspecify.annotations.NonNull;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Assumptions;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.Arguments;
import org.junit.jupiter.params.provider.MethodSource;

/**
 * This class provides regression tests for KeY Taclets.
 *
 * <p>
 * This class uses a default project to bootstrap a
 * {@link de.uka.ilkd.key.control.KeYEnvironment} and prints all registered taclets with the
 * {@link LogicPrinter} in parseable (non-pretty) mode. The printout of each taclet is compared to
 * the latest version defined in {@code taclets.old.txt}. In addition, every entry is parsed again
 * and re-printed; the re-print must be structurally identical to the original taclet.
 * </p>
 *
 * <h2>How to update {@code taclet.old.txt} efficiently.</h2>
 * <p>
 * You can generate a new oracle easily by invoking the disabled test-method
 * {@link #createOracle()}. This method generates the {@code taclets.new.txt} file. Then, you
 * should use a diff-tool to compare the changes or directly overwrite {@code taclets.old.txt} with
 * the new representations.
 *
 * @author Alexander Weigl
 * @version 1 (5/5/20)
 */
public class TestTacletEquality {
    public static Stream<Arguments> createCases() throws IOException {
        InputStream is = TestTacletEquality.class.getResourceAsStream("taclets.old.txt");
        Assumptions.assumeTrue(is != null);
        var seq = Stream.<Arguments>builder();
        try (BufferedReader r =
            new BufferedReader(new InputStreamReader(is, StandardCharsets.UTF_8))) {
            String tmp;
            while ((tmp = r.readLine()) != null) {
                if (tmp.trim().isEmpty()) {
                    continue;
                }
                if (tmp.startsWith("#")) {
                    continue;
                }
                if (tmp.startsWith("== ")) {
                    StringBuilder expected = new StringBuilder();
                    int nameEnd = tmp.indexOf(' ', 4);
                    String name = tmp.substring(3, nameEnd + 1).trim();
                    while ((tmp = r.readLine()) != null) {
                        if (tmp.trim().isEmpty()) {
                            continue;
                        }
                        if (tmp.startsWith("#")) {
                            continue;
                        }
                        if (tmp.startsWith("---")) {
                            seq.add(Arguments.of(name, expected.toString()));
                            break;
                        }
                        expected.append(tmp).append("\n");
                    }
                }
            }
        }
        return seq.build();
    }

    private static InitConfig initConfig;
    private static InitConfig parseConfig;

    @BeforeAll
    static void setUp() throws Exception {
        Path file = HelperClassForTests.TESTCASE_DIRECTORY.resolve("merge/gcd.closed.proof");
        if (initConfig == null) {
            ProblemLoaderControl control = new DefaultUserInterfaceControl(null);
            SingleThreadProblemLoader loader =
                new SingleThreadProblemLoader(file, null, null, null,
                    JavaProfile.getDefaultInstance(), true, control, false, null);
            loader.load();
            initConfig = loader.getInitConfig();
            parseConfig = initConfig.copy();
            registerGenericSorts(parseConfig);
            // uncomment the line, if you want to generate a new oracle file
            // createNewOracle();
        }
    }

    /**
     * Makes the generic sorts used by the base taclets available for re-parsing. The generic sorts
     * are deliberately removed from the base namespace after loading the standard rules, so the
     * printed taclets can only be parsed if their generic sorts are registered again.
     */
    private static void registerGenericSorts(InitConfig config) {
        for (Taclet taclet : initConfig.activatedTaclets()) {
            for (GenericSort sort : genericSorts(taclet)) {
                if (config.namespaces().sorts().lookup(sort.name()) == null) {
                    config.namespaces().sorts().add(sort);
                }
            }
        }
    }

    private static Set<GenericSort> genericSorts(Taclet taclet) {
        Set<GenericSort> result = new LinkedHashSet<>();
        var collector = new UninstantiatedGenericSortCollector(
            SVInstantiations.EMPTY_SVINSTANTIATIONS);
        collector.visit(taclet, true);
        result.addAll(collector.getSortList());

        for (SchemaVariable sv : taclet.collectSchemaVars()) {
            if (!(sv instanceof de.uka.ilkd.key.logic.op.ModalOperatorSV)) {
                collectGenericSorts(sv.sort(), result);
            }
        }
        for (NewVarcond nvc : taclet.varsNew()) {
            collectGenericSorts(nvc.getSchemaVariable().sort(), result);
            if (nvc instanceof de.uka.ilkd.key.rule.NewVarcond keyVarcond
                    && keyVarcond.getType() != null) {
                collectGenericSorts(keyVarcond.getType().getSort(), result);
            }
        }
        for (NotFreeIn pair : taclet.varsNotFreeIn()) {
            collectGenericSorts(pair.first().sort(), result);
            collectGenericSorts(pair.second().sort(), result);
        }
        for (NewDependingOn pair : taclet.varsNewDependingOn()) {
            collectGenericSorts(pair.first().sort(), result);
            collectGenericSorts(pair.second().sort(), result);
        }
        for (var condition : taclet.getVariableConditions()) {
            collectGenericSortsFromObject(condition, result);
        }
        if (taclet.hasTrigger()) {
            collectGenericSortsFromObject(taclet.getTrigger(), result);
        }
        return result;
    }

    private static void collectGenericSorts(Sort sort, Set<GenericSort> result) {
        if (sort instanceof GenericSort genericSort) {
            result.add(genericSort);
        } else if (sort instanceof ParametricSortInstance parametricSort) {
            for (var argument : parametricSort.getArgs()) {
                collectGenericSorts(argument.sort(), result);
            }
        }
    }

    private static void collectGenericSortsFromObject(Object object, Set<GenericSort> result) {
        collectGenericSortsFromObject(object, result,
            Collections.newSetFromMap(new IdentityHashMap<>()));
    }

    private static void collectGenericSortsFromObject(Object object, Set<GenericSort> result,
            Set<Object> visited) {
        if (object == null || visited.contains(object)) {
            return;
        }
        if (object instanceof Sort sort) {
            collectGenericSorts(sort, result);
            return;
        }
        if (object instanceof String || object instanceof Number || object instanceof Boolean
                || object instanceof Enum<?>) {
            return;
        }
        if (object instanceof Map<?, ?> map) {
            for (Object value : map.values()) {
                collectGenericSortsFromObject(value, result, visited);
            }
            return;
        }
        if (object instanceof Iterable<?> iterable) {
            for (Object element : iterable) {
                collectGenericSortsFromObject(element, result, visited);
            }
            return;
        }
        Class<?> clazz = object.getClass();
        if (clazz.isArray()) {
            for (int i = 0; i < java.lang.reflect.Array.getLength(object); i++) {
                collectGenericSortsFromObject(java.lang.reflect.Array.get(object, i), result,
                    visited);
            }
            return;
        }
        if (!clazz.getName().startsWith("de.uka.ilkd.key.rule")) {
            return;
        }
        visited.add(object);
        for (var field : clazz.getDeclaredFields()) {
            if (java.lang.reflect.Modifier.isStatic(field.getModifiers())
                    || field.getType().isPrimitive()) {
                continue;
            }
            try {
                field.setAccessible(true);
                collectGenericSortsFromObject(field.get(object), result, visited);
            } catch (ReflectiveOperationException | RuntimeException e) {
                // best effort: inaccessible fields cannot contribute sorts
            }
        }
    }

    /**
     * Prints a taclet in parseable KeY rule syntax. Choice restrictions are not part of the
     * taclet declaration; {@link #printOracleEntry(Taclet)} adds them in a {@code \rules} block.
     */
    private static String printTaclet(Taclet taclet) {
        var notation = new NotationInfo();
        notation.refresh(initConfig.getServices(), false, false, false);
        var printer = LogicPrinter.purePrinter(notation, initConfig.getServices());
        printer.printTaclet(taclet);
        return printer.result().strip();
    }

    /**
     * Prints an oracle entry: the taclet, wrapped in a {@code \rules} block when it is restricted
     * to specific choices.
     */
    private static String printOracleEntry(Taclet taclet) {
        String printed = printTaclet(taclet);
        ChoiceExpr choices = taclet.getChoices();
        if (choices == null || choices.equals(ChoiceExpr.TRUE)) {
            return printed;
        }
        String expression = choices.toString();
        if (!expression.startsWith("(") || !expression.endsWith(")")) {
            expression = "(" + expression + ")";
        }
        return "\\rules " + expression + " {\n  " + printed.replace("\n", "\n  ") + ";\n}";
    }

    private static Taclet parseTaclet(String text) throws IOException {
        String source = text.strip();
        if (!source.startsWith("\\rules")) {
            source = "\\rules { " + source + "; }";
        }
        var io = new KeyIO(parseConfig.getServices(), parseConfig.namespaces());
        List<Taclet> taclets = io.load(source).loadComplete();
        return taclets.get(0);
    }

    @SuppressWarnings("unused")
    public static void createNewOracle() {
        var path = Paths.get("src/test/resources/de/uka/ilkd/key/nparser/taclets.new.txt");
        var taclets = new ArrayList<>(initConfig.activatedTaclets());
        // sort by name
        taclets.sort(Comparator.comparing(it -> it.name().toString()));

        try (var out =
            new PrintWriter(Files.newBufferedWriter(path, StandardCharsets.UTF_8))) {
            out.write(
                "# This files contains representation of taclets, which are accepted and revised.\n");
            out.write("# Each taclet is printed in parseable KeY rule syntax.\n");
            out.format("# Date: %s\n\n", new Date());
            for (Taclet taclet : taclets) {
                out.format("== %s (%s) =========================================\n", taclet.name(),
                    taclet.displayName());
                for (String line : printOracleEntry(taclet).split("\n", -1)) {
                    out.println(line.stripTrailing());
                }
                out.format("-----------------------------------------------------\n");
            }
        } catch (IOException e) {
            Assertions.fail("Exception for opening " + path, e);
        }
    }

    // @Test
    public void createOracle() {
        createNewOracle();
    }

    @Test
    public void testWholeOracleIsOneParseableFile() throws IOException {
        var cases = createCases().toList();
        var source = new StringBuilder();
        for (Arguments arguments : cases) {
            String text = (String) arguments.get()[1];
            if (text.strip().startsWith("\\rules")) {
                source.append(text).append('\n');
            } else {
                source.append("\\rules {\n").append(text).append(";\n}\n");
            }
        }

        var io = new KeyIO(parseConfig.getServices(), parseConfig.namespaces());
        List<Taclet> parsed = io.load(source.toString()).loadComplete();
        Assertions.assertEquals(cases.size(), parsed.size(),
            "Every oracle entry must parse from one KeY document");
    }

    @ParameterizedTest
    @MethodSource("createCases")
    public void testEquality(String name, String expected) {
        Taclet taclet = findTaclet(name);
        Assumptions.assumeTrue(taclet != null);

        String printed = printOracleEntry(taclet);
        assertEquals(expected, printed);

        Taclet reparsed;
        try {
            reparsed = parseTaclet(expected);
        } catch (IOException e) {
            throw new AssertionError("Oracle entry for " + name + " is not parseable", e);
        }
        assertEquals(printed, printOracleEntry(reparsed));
    }


    private void assertEquals(String expected, String actual) {
        Assertions.assertEquals(normalise(expected), normalise(actual));
    }

    private @NonNull String normalise(String text) {
        return text.replaceAll("\\s+", " ").trim();
    }

    final HashMap<String, Taclet> cache = new HashMap<>();

    private Taclet findTaclet(String name) {
        if (cache.isEmpty()) {
            for (Taclet taclet : initConfig.activatedTaclets()) {
                cache.put(taclet.name().toString(), taclet);
            }
        }
        return cache.get(name);
    }
}
