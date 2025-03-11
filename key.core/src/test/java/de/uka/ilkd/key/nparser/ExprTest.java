/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.nparser;

import java.io.IOException;
import java.net.URL;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.util.parsing.BuildingException;

import org.junit.jupiter.api.Assumptions;
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

    @ParameterizedTest
    @CsvFileSource(resources = "exprs.txt", delimiter = '^')
    public void parseAndVisit(String expr) throws IOException {
        Assumptions.assumeFalse(expr.startsWith("#"));
        KeyIO io = getIo();
        try {
            Term actual = io.parseExpression(expr);
            assertNotNull(actual);
            LOGGER.info("Term: {}", actual);
        } catch (BuildingException e) {
            DebugKeyLexer.debug(expr);
        }
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
