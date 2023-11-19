/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.nparser;

import java.io.IOException;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.lang.reflect.Field;
import java.net.URL;
import java.util.*;
import java.util.stream.Collectors;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.overop.OperatorInfo;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.proof.init.JavaProfile;

import org.jspecify.annotations.NonNull;
import org.junit.jupiter.api.Assumptions;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.CsvFileSource;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * @author Alexander Weigl
 * @version 1 (17.10.19)
 */
public class ExprTest {
    private static final Logger LOGGER = LoggerFactory.getLogger(ExprTest.class);

    @Test
    public void printOpTable() throws IllegalAccessException {
        var sw = new StringWriter();
        var out = new PrintWriter(sw);

        var map = new TreeMap<Integer, List<OperatorInfo>>();
        for (OperatorInfo value : OperatorInfo.values()) {
            if (!map.containsKey(value.getPrecedence()))
                map.put(value.getPrecedence(), new LinkedList<>());
            map.get(value.getPrecedence()).add(value);
        }
        out.println("| Level | Operators |");
        out.println(":-: | -----------");
        var levels = Arrays.stream(NotationInfo.class.getFields())
                .filter(it -> it.getName().startsWith("PRIORITY_"))
                .sorted(Comparator.comparing(it -> {
                    try {
                        return it.getInt(null);
                    } catch (IllegalAccessException e) {
                        throw new RuntimeException(e);
                    }
                })).toList();

        for (Field f : levels) {
            int level = f.getInt(null);
            var values = map.get(level);
            var a = "";
            if (values != null)
                a = values.stream()
                        .flatMap(it -> it.getNames().stream())
                        .map(it -> "`" + it + "`")
                        .collect(Collectors.joining(" "));
            out.format("| %d | %s | %s |\n",
                level, f.getName().substring(9),
                a);
        }
        System.out.println(sw);
    }


    @ParameterizedTest
    @CsvFileSource(resources = "exprs.txt", delimiter = '^')
    public void parseAndVisit(String expr) throws IOException {
        Assumptions.assumeFalse(expr.startsWith("#"));
        KeyIO io = getIo();
        @NonNull
        Term actual = io.parseExpression(expr);
        assertNotNull(actual);
        LOGGER.info("Actual Term: {}", actual);

        LOGGER.warn("Actual Term: {}",
            LogicPrinter.quickPrintTerm(actual, io.getServices(), true, true));
    }

    private KeyIO getIo() throws IOException {
        Services services = new Services(new JavaProfile());
        String p = "/de/uka/ilkd/key/proof/rules/ldt.key";
        URL url = getClass().getResource(p);
        Assumptions.assumeTrue(url != null);
        KeyIO io = new KeyIO(services);
        io.load(url).parseFile().loadDeclarations().loadSndDegreeDeclarations();

        NamespaceBuilder nssb = new NamespaceBuilder(services.getNamespaces());
        nssb.addVariable("aa", "int").addVariable("bb", "int").addVariable("cc", "int")
                .addProgramVariable("int", "x");

        // Without this call, the LDTs are not available to the expression
        // builder. Probably a problem of the mocking here. (MU)
        services.getTypeConverter().init();

        return io;
    }


    @ParameterizedTest
    @CsvFileSource(resources = "precedence_tests.txt", delimiterString = ":::")
    void precedenceStrongArithmetic(String actual, String expected) throws IOException {
        var io = getIo();
        var e = io.parseExpression(expected);
        var a = io.parseExpression(actual);
        assertEquals(e, a);
    }

}
