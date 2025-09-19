/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.nparser;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.Collection;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.rule.Taclet;

import org.key_project.logic.Name;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;

/**
 * Tests for handling of abstract datatypes in KeY files.
 */
public class AdtTests {
    private static final String EXPECTED_PRED_DEC_SUCC = """
            DT_Nat#Dec_pred#succ {
            \\find(pred(succ(pred_sv)))
            \\sameUpdateLevel\\replacewith(pred_sv)\s
            \\heuristics(simplify)
            Choices: true}""";
    private static final String EXPECTED_PRED_DECEQ_SUCC = """
            DT_Nat#Dec_pred#succ#EQ {
            \\assumes ([equals(succ(pred_sv),pred_x)]==>[])\s
            \\find(pred(pred_x))
            \\sameUpdateLevel\\replacewith(pred_sv)\s
            \\heuristics(simplify)
            Choices: true}""";

    @Test
    public void destructorTest() throws ProblemLoaderException {
        var path = Paths.get("../key.ui/examples/standard_key/adt/dt_nat.key");
        var env = KeYEnvironment.load(path);
        var taclets = env.getInitConfig().activatedTaclets();

        for (Taclet taclet : taclets) {
            if (taclet.name().toString().contains("_Dec"))
                System.out.println(taclet.name());
        }

        var predDecsucc = get("DT_Nat#Dec_pred#succ", taclets);
        var predDecEqSucc = get("DT_Nat#Dec_pred#succ#EQ", taclets);

        Assertions.assertEquals(EXPECTED_PRED_DEC_SUCC, predDecsucc.toString());
        Assertions.assertEquals(EXPECTED_PRED_DECEQ_SUCC, predDecEqSucc.toString());

    }

    /*
     * Test for a non-recursive constructor. The generated taclet must not contain an induction
     * hypothesis.
     * See #3661
     */
    @Test
    public void nonRecursiveConstructorTest() throws ProblemLoaderException, IOException {
        var path = Paths.get("../key.ui/examples/standard_key/adt/dt_nonrec.key");
        var env = KeYEnvironment.load(path);
        var taclets = env.getInitConfig().activatedTaclets();
        String expected = Files.lines(path)
                .filter(l -> l.startsWith("//!"))
                .map(l -> l.substring(4))
                .collect(java.util.stream.Collectors.joining("\n"));

        var consTaclet = get("DT_NonRec#Dec_nonrecarg#b", taclets);
        // There are spaces before linebreaks. Better remove them for the comparison.
        Assertions.assertEquals(expected, consTaclet.toString().replaceAll(" +\n", "\n"));
    }


    private Taclet get(String name, Collection<Taclet> taclets) {
        var n = new Name(name);
        var t = taclets.stream().filter(it -> n.equals(it.name())).findAny().orElse(null);
        Assertions.assertNotNull(t);
        return t;
    }
}
