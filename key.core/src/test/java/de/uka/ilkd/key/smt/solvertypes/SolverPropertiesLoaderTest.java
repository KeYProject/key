/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.smt.solvertypes;

import de.uka.ilkd.key.settings.Configuration;

import org.junit.jupiter.api.Test;

import static org.assertj.core.api.Assertions.assertThat;
import static org.junit.jupiter.api.Assertions.*;

/**
 * @author Alexander Weigl
 * @version 1 (6/14/25)
 */
class SolverPropertiesLoaderTest {
    private Configuration config = SolverPropertiesLoader.loadSolvers();

    @Test
    void loadCVC4() {
        var cvc4 = config.getSection("CVC4");
        assertNotNull(cvc4);
        assertEquals("de.uka.ilkd.key.smt.communication.CVC4Socket", cvc4.getString("socketClass"));
        assertEquals("CVC4", cvc4.getString("name"));
        assertTrue(cvc4.getBool("experimental"));
        assertEquals("--no-print-success --produce-models --no-interactive --lang smt2",
            cvc4.getString("params"));
        assertEquals("--version", cvc4.getString("version"));
        assertEquals("cvc4", cvc4.getString("command"));
        assertEquals(-1, cvc4.getInt("timeout"));

        assertThat(cvc4.getStringList("handlers"))
                .containsExactly(
                    "de.uka.ilkd.key.smt.newsmt2.BooleanConnectiveHandler",
                    "de.uka.ilkd.key.smt.newsmt2.PolymorphicHandler",
                    "de.uka.ilkd.key.smt.newsmt2.QuantifierHandler",
                    "de.uka.ilkd.key.smt.newsmt2.LogicalVariableHandler",
                    "de.uka.ilkd.key.smt.newsmt2.NumberConstantsHandler",
                    "de.uka.ilkd.key.smt.newsmt2.IntegerOpHandler",
                    "de.uka.ilkd.key.smt.newsmt2.InstanceOfHandler",
                    "de.uka.ilkd.key.smt.newsmt2.CastHandler",
                    "de.uka.ilkd.key.smt.newsmt2.SumProdHandler",
                    "de.uka.ilkd.key.smt.newsmt2.UpdateHandler",
                    "de.uka.ilkd.key.smt.newsmt2.FieldConstantHandler",
                    "de.uka.ilkd.key.smt.newsmt2.FloatHandler",
                    "de.uka.ilkd.key.smt.newsmt2.CastingFunctionsHandler",
                    "de.uka.ilkd.key.smt.newsmt2.DefinedSymbolsHandler",
                    "de.uka.ilkd.key.smt.newsmt2.UninterpretedSymbolsHandler");
    }

    @Test
    void loadCVC4Legacy() {
        var cvc4 = config.getSection("CVC4Legacy");
        assertNotNull(cvc4);
        assertEquals("de.uka.ilkd.key.smt.communication.CVC4Socket", cvc4.getString("socketClass"));
        assertEquals("CVC4 (Legacy Translation)", cvc4.getString("name"));
        assertEquals("de.uka.ilkd.key.smt.SmtLib2Translator", cvc4.getString("translatorClass"));
        assertTrue(cvc4.getBool("experimental"));
        assertEquals("--no-print-success --produce-models --no-interactive --lang smt2",
            cvc4.getString("params"));
        assertEquals("--version", cvc4.getString("version"));
        assertEquals("cvc4", cvc4.getString("command"));
        assertEquals(-1, cvc4.getInt("timeout"));
    }

    @Test
    void loadCVC5() {
        var cvc5 = config.getSection("CVC5");
        assertNotNull(cvc5);
        assertEquals("de.uka.ilkd.key.smt.communication.Cvc5Socket", cvc5.getString("socketClass"));
        assertEquals("cvc5", cvc5.getString("name"));
        assertEquals("--no-interactive --produce-models --lang smt2", cvc5.getString("params"));
        assertEquals("--version", cvc5.getString("version"));
        assertEquals("cvc5", cvc5.getString("command"));
        assertEquals(-1, cvc5.getInt("timeout"));
        assertThat(cvc5.getStringList("handlerOptions")).containsExactly("getUnsatCore");


        assertThat(cvc5.getStringList("handlers"))
                .containsExactly(
                    "de.uka.ilkd.key.smt.newsmt2.BooleanConnectiveHandler",
                    "de.uka.ilkd.key.smt.newsmt2.PolymorphicHandler",
                    "de.uka.ilkd.key.smt.newsmt2.QuantifierHandler",
                    "de.uka.ilkd.key.smt.newsmt2.LogicalVariableHandler",
                    "de.uka.ilkd.key.smt.newsmt2.NumberConstantsHandler",
                    "de.uka.ilkd.key.smt.newsmt2.IntegerOpHandler",
                    "de.uka.ilkd.key.smt.newsmt2.InstanceOfHandler",
                    "de.uka.ilkd.key.smt.newsmt2.CastHandler",
                    "de.uka.ilkd.key.smt.newsmt2.SumProdHandler",
                    "de.uka.ilkd.key.smt.newsmt2.UpdateHandler",
                    "de.uka.ilkd.key.smt.newsmt2.FieldConstantHandler",
                    "de.uka.ilkd.key.smt.newsmt2.FloatHandler",
                    "de.uka.ilkd.key.smt.newsmt2.CastingFunctionsHandler",
                    "de.uka.ilkd.key.smt.newsmt2.DefinedSymbolsHandler",
                    "de.uka.ilkd.key.smt.newsmt2.UninterpretedSymbolsHandler");
    }

    @Test
    void loadPrincess() {
        var princess = config.getSection("Princess");


        assertNotNull(princess);
        assertEquals("2021-11-15", princess.getString("minVersion"));
        assertEquals("Princess", princess.getString("name"));
        assertFalse(princess.getBool("experimental", false));
        assertEquals("+stdin", princess.getString("params"));
        assertEquals("+version", princess.getString("version"));
        assertEquals("princess", princess.getString("command"));
        assertEquals(-1, princess.getInt("timeout"));

        assertThat(princess.getStringList("handlers"))
                .containsExactly(
                    "de.uka.ilkd.key.smt.newsmt2.BooleanConnectiveHandler",
                    "de.uka.ilkd.key.smt.newsmt2.PolymorphicHandler",
                    "de.uka.ilkd.key.smt.newsmt2.QuantifierHandler",
                    "de.uka.ilkd.key.smt.newsmt2.LogicalVariableHandler",
                    "de.uka.ilkd.key.smt.newsmt2.NumberConstantsHandler",
                    "de.uka.ilkd.key.smt.newsmt2.IntegerOpHandler",
                    "de.uka.ilkd.key.smt.newsmt2.InstanceOfHandler",
                    "de.uka.ilkd.key.smt.newsmt2.CastHandler",
                    "de.uka.ilkd.key.smt.newsmt2.SumProdHandler",
                    "de.uka.ilkd.key.smt.newsmt2.UpdateHandler",
                    "de.uka.ilkd.key.smt.newsmt2.FieldConstantHandler",
                    "de.uka.ilkd.key.smt.newsmt2.FloatHandler",
                    "de.uka.ilkd.key.smt.newsmt2.CastingFunctionsHandler",
                    "de.uka.ilkd.key.smt.newsmt2.DefinedSymbolsHandler",
                    "de.uka.ilkd.key.smt.newsmt2.UninterpretedSymbolsHandler");

    }

    @Test
    void loadZ3() {
        var z3 = config.getSection("Z3");


        assertNotNull(z3);
        assertEquals("Z3 version 4.4.1", z3.getString("minVersion"));
        assertEquals("Z3", z3.getString("name"));
        assertFalse(z3.getBool("experimental", false));
        assertEquals("-in -smt2", z3.getString("params"));
        assertEquals("--version", z3.getString("version"));
        assertEquals("z3", z3.getString("command"));
        assertEquals(-1, z3.getInt("timeout"));
        assertThat(z3.getStringList("handlerOptions")).containsExactly("getUnsatCore");

        assertThat(z3.getStringList("handlers")).containsExactly(
            "de.uka.ilkd.key.smt.newsmt2.BooleanConnectiveHandler",
            "de.uka.ilkd.key.smt.newsmt2.PolymorphicHandler",
            "de.uka.ilkd.key.smt.newsmt2.QuantifierHandler",
            "de.uka.ilkd.key.smt.newsmt2.LogicalVariableHandler",
            "de.uka.ilkd.key.smt.newsmt2.NumberConstantsHandler",
            "de.uka.ilkd.key.smt.newsmt2.IntegerOpHandler",
            "de.uka.ilkd.key.smt.newsmt2.InstanceOfHandler",
            "de.uka.ilkd.key.smt.newsmt2.CastHandler",
            "de.uka.ilkd.key.smt.newsmt2.SumProdHandler",
            "de.uka.ilkd.key.smt.newsmt2.UpdateHandler",
            "de.uka.ilkd.key.smt.newsmt2.FieldConstantHandler",
            "de.uka.ilkd.key.smt.newsmt2.FloatHandler",
            "de.uka.ilkd.key.smt.newsmt2.CastingFunctionsHandler",
            "de.uka.ilkd.key.smt.newsmt2.DefinedSymbolsHandler",
            "de.uka.ilkd.key.smt.newsmt2.UninterpretedSymbolsHandler");
    }

    @Test
    void loadZ3CE() {
        var z3 = config.getSection("Z3_CE");
        assertNotNull(z3);
        assertEquals("Z3_CE", z3.getString("name"));
        assertEquals("de.uka.ilkd.key.smt.communication.Z3CESocket", z3.getString("socketClass"));
        assertEquals("de.uka.ilkd.key.smt.SmtLib2Translator", z3.getString("translatorClass"));
        assertEquals("-in -smt2", z3.getString("params"));
        assertEquals("--version", z3.getString("version"));
        assertEquals("z3", z3.getString("command"));
        assertEquals(-1, z3.getInt("timeout"));
    }

    @Test
    void loadZ3FP() {
        var z3 = config.getSection("Z3_FloatingPoint");

        assertNotNull(z3);
        assertEquals("Z3_FP", z3.getString("name"));
        assertEquals("-in -smt2", z3.getString("params"));
        assertEquals("--version", z3.getString("version"));
        assertEquals("z3", z3.getString("command"));
        assertEquals(-1, z3.getInt("timeout"));
        assertThat(z3.getStringList("handlerOptions")).containsExactly("getUnsatCore");

        assertThat(z3.getStringList("handlers")).containsExactly(
            "de.uka.ilkd.key.smt.newsmt2.BooleanConnectiveHandler",
            "de.uka.ilkd.key.smt.newsmt2.FloatHandler",
            "de.uka.ilkd.key.smt.newsmt2.FloatRemainderHandler");
    }

    @Test
    void loadZ3QF() {
        var z3 = config.getSection("Z3_QF");


        assertNotNull(z3);
        assertEquals("Z3_QF", z3.getString("name"));
        assertEquals("-in -smt2", z3.getString("params"));
        assertEquals("--version", z3.getString("version"));
        assertEquals("z3", z3.getString("command"));
        assertEquals(-1, z3.getInt("timeout"));
        assertThat(z3.getStringList("handlerOptions")).containsExactly("getUnsatCore");

        assertThat(z3.getStringList("handlers")).containsExactly(
            "de.uka.ilkd.key.smt.newsmt2.BooleanConnectiveHandler",
            "de.uka.ilkd.key.smt.newsmt2.PolymorphicHandler",
            "de.uka.ilkd.key.smt.newsmt2.QuantifierHandler",
            "de.uka.ilkd.key.smt.newsmt2.LogicalVariableHandler",
            "de.uka.ilkd.key.smt.newsmt2.NumberConstantsHandler",
            "de.uka.ilkd.key.smt.newsmt2.IntegerOpHandler",
            "de.uka.ilkd.key.smt.newsmt2.InstanceOfHandler",
            "de.uka.ilkd.key.smt.newsmt2.CastHandler",
            "de.uka.ilkd.key.smt.newsmt2.SumProdHandler",
            "de.uka.ilkd.key.smt.newsmt2.UpdateHandler",
            "de.uka.ilkd.key.smt.newsmt2.FieldConstantHandler",
            "de.uka.ilkd.key.smt.newsmt2.FloatHandler",
            "de.uka.ilkd.key.smt.newsmt2.CastingFunctionsHandler",
            "de.uka.ilkd.key.smt.newsmt2.DefinedSymbolsHandler",
            "de.uka.ilkd.key.smt.newsmt2.UninterpretedSymbolsHandler");
    }

    @Test
    void loadZ3Legacy() {
        var z3 = config.getSection("Z3Legacy");
        assertNotNull(z3);
        assertEquals("Z3 (Legacy Translation)", z3.getString("name"));
        assertEquals("de.uka.ilkd.key.smt.SmtLib2Translator", z3.getString("translatorClass"));
        assertTrue(z3.getBool("experimental"));
        assertEquals("-in -smt2", z3.getString("params"));
        assertEquals("--version", z3.getString("version"));
        assertEquals("z3", z3.getString("command"));
        assertEquals(-1, z3.getInt("timeout"));

    }
}
