/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.tacletbuilder;

import java.io.File;
import java.io.IOException;
import java.util.List;
import java.util.Objects;
import java.util.stream.Collectors;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.macros.scripts.ProofScriptEngine;
import de.uka.ilkd.key.macros.scripts.ScriptException;
import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.rule.tacletbuilder.branchlabel.BranchNamingFunctions;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.CsvSource;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * @author Alexander Weigl
 * @version 1 (1/15/22)
 */
class BranchNamingFunctionsTest {

    @ParameterizedTest
    @CsvSource(delimiter = '!', value = {
        "\\test![\\test]",
        "\\test(a)![\\test|a]",
        "\\test(a,b)![\\test|a|b]",
        "\\test(    a, b  )![\\test|a|b]",
        "\\test(    a, b  )XX\\test(a) test: \\test(a,b,c,d)end![\\test|a|b]XX[\\test|a] test: [\\test|a|b|c|d]end" })
    void parseNamingFunctionsNames(String input, String exp) {
        assertEquals(exp, parseAndEval(input));
    }

    private String parseAndEval(String label) {
        Services services = new Services(JavaProfile.getDefaultProfile());
        var fn = BranchNamingFunctions.find(label);
        return fn.getName(null, null, null, null);
    }

    @Test
    void nameLabelInProof()
            throws ProblemLoaderException, ScriptException, IOException, InterruptedException {
        var env = KeYEnvironment
                .load(new File("src/test/resources/de/uka/ilkd/key/rule/tacletbuilder/split.key"));
        var proof = env.getLoadedProof();
        var engine = new ProofScriptEngine("rule andRight; rule andRight;",
            new Location(null, Position.fromOneZeroBased(1, 1)));
        engine.execute(env.getUi(), proof);
        System.out.println(proof);
        List<String> labels = proof.root().subtreeStream()
                .map(it -> it.getNodeInfo().getBranchLabel())
                .filter(Objects::nonNull)
                .collect(Collectors.toList());
        var actual = labels.toString();
        assertEquals("[a<<name(\"labelA\")>> & c<<name(\"labelC\")>>, labelA, labelC, labelB]",
            actual);
    }
}
