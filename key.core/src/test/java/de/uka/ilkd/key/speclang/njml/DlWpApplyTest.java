/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.speclang.njml;

import java.io.IOException;
import java.io.InputStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.nparser.KeyIO;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.speclang.Contract;

import org.key_project.logic.op.Function;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Tests for the JML escape {@code \dl_wp_apply(this, arg)} (Csiky, ch. 5,
 * appendix A.1): the escape must lex and parse, translate into the JavaDL
 * predicate {@code wp_apply(...)}, and the accompanying taclet file
 * {@code keyForLambda.key} must be parseable with the KeY rule parser.
 */
class DlWpApplyTest {

    /**
     * Resource path of the standalone rule file with the {@code wp_def} and
     * {@code wp_dep_contract} taclets (thesis appendix A.1).
     */
    private static final String KEY_FOR_LAMBDA_RULES =
        "/de/uka/ilkd/key/proof/rules/weiglLambda/keyForLambda.key";

    /** Functional interface with a JML contract using {@code \dl_wp_apply}. */
    private static final String INT_FUNCTION_JAVA = """
            interface IntFunction {
                /*@ public normal_behaviour
                  @ requires \\dl_wp_apply(this, arg);
                  @ ensures \\result == apply(arg);
                  @*/
                public int apply(int arg);
            }
            """;

    /**
     * Same interface without any JML annotation. Loading this file translates
     * no contracts, so no {@code wp_apply} symbol is registered and the taclet
     * file's {@code \predicates} declaration (which must be parsed before the
     * first JML translation, see the comment in keyForLambda.key) can be
     * registered against the environment's namespaces.
     */
    private static final String INT_FUNCTION_PLAIN_JAVA = """
            interface IntFunction {
                public int apply(int arg);
            }
            """;

    @TempDir
    Path tempDir;

    private Path writeIntFunction(String source) throws IOException {
        Path javaFile = tempDir.resolve("IntFunction.java");
        Files.writeString(javaFile, source);
        return javaFile;
    }

    /**
     * Parses {@code keyForLambda.key} with the KeY rule parser against the
     * given environment (its Java model provides the {@code IntFunction}
     * interface used by the {@code wp_def} taclet). The declaration of the
     * {@code wp_apply} predicate is added to the environment's namespaces, as
     * it would be when the rule file is loaded together with a proof.
     */
    private static List<Taclet> parseWpApplyRules(KeYEnvironment<?> env) throws IOException {
        String rules;
        try (InputStream in = DlWpApplyTest.class.getResourceAsStream(KEY_FOR_LAMBDA_RULES)) {
            assertNotNull(in, "Rule file resource '" + KEY_FOR_LAMBDA_RULES + "' not found");
            rules = new String(in.readAllBytes(), StandardCharsets.UTF_8);
        }
        final NamespaceSet nss = env.getInitConfig().namespaces();
        KeyIO io = new KeyIO(env.getServices(), nss);
        return io.load(rules).loadComplete();
    }

    /** @return true if the term tree contains a function/predicate with the given name */
    private static boolean containsFunction(JTerm term, String name) {
        if (term.op() instanceof Function f && f.name().toString().equals(name)) {
            return true;
        }
        for (int i = 0; i < term.arity(); i++) {
            if (containsFunction(term.sub(i), name)) {
                return true;
            }
        }
        return false;
    }

    /**
     * The taclet file with the thesis appendix A.1 rules must parse with the
     * KeY rule parser (against a Java model that contains the functional
     * interface {@code IntFunction}).
     */
    @Test
    void wpRulesFromAppendixParse() throws Exception {
        // IntFunction must exist as a Java type for the wp_def taclet, but the
        // file must not carry any JML contract: contract translation would
        // register wp_apply on demand and clash with the \predicates declaration.
        final Path javaFile = writeIntFunction(INT_FUNCTION_PLAIN_JAVA);
        try (KeYEnvironment<?> env = KeYEnvironment.load(javaFile)) {
            final List<Taclet> taclets = parseWpApplyRules(env);
            assertEquals(2, taclets.size(),
                "Expected the two taclets wp_dep_contract and wp_def, got: " + taclets);
            assertEquals("wp_dep_contract", taclets.get(0).name().toString());
            assertEquals("wp_def", taclets.get(1).name().toString());
        }
    }

    /**
     * A JML contract containing {@code requires \dl_wp_apply(this, arg);} on a
     * functional interface method must parse and translate into a term
     * {@code wp_apply(heap, this, arg)}.
     */
    @Test
    void dlWpApplyInRequiresTranslates() throws Exception {
        // Loading a class whose JML contract uses \dl_wp_apply translates the
        // contract immediately; JmlTermFactory then registers the wp_apply
        // predicate on demand (Option A). No rule loading happens here, so the
        // on-demand registration does not clash with a \predicates declaration.
        final Path javaFile = writeIntFunction(INT_FUNCTION_JAVA);
        try (KeYEnvironment<?> env = KeYEnvironment.load(javaFile)) {
            final Services services = env.getServices();

            final List<Contract> contracts = env.getProofContracts();
            assertFalse(contracts.isEmpty(),
                "Expected at least one contract extracted from " + javaFile);

            final Contract applyContract = contracts.stream()
                    .filter(c -> c.getTarget().name().toString().contains("apply"))
                    .findFirst()
                    .orElseThrow(() -> new AssertionError(
                        "No contract for method apply found, contracts: " + contracts));

            final Contract.OriginalVariables orig = applyContract.getOrigVars();
            // OriginalVariables intentionally stores no heap; use the standard base heap
            // program variable of the heap LDT (cf. DependencyContractPO).
            final var heap = services.getTypeConverter().getHeapLDT().getHeap();
            final JTerm pre = applyContract.getPre(heap, orig.self, orig.params, orig.atPres,
                services);
            assertTrue(containsFunction(pre, "wp_apply"),
                "requires clause should contain function wp_apply, but was: " + pre);
        }
    }
}
