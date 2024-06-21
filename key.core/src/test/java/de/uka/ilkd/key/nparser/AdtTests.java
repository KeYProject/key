/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.nparser;

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
            pred_Dec_succ {
            \\find(pred(succ(pred_sv)))
            \\sameUpdateLevel\\replacewith(pred_sv)\s

            Choices: true}""";
    private static final String EXPECTED_PRED_DECEQ_SUCC = """
            pred_DecEQ_succ {
            \\assumes ([equals(pred_x,succ(pred_sv))]==>[])\s
            \\find(pred(pred_x))
            \\sameUpdateLevel\\replacewith(pred_sv)\s

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

        var predDecsucc = get("pred_Dec_succ", taclets);
        var predDecEqSucc = get("pred_DecEQ_succ", taclets);

        Assertions.assertEquals(EXPECTED_PRED_DEC_SUCC, predDecsucc.toString());
        Assertions.assertEquals(EXPECTED_PRED_DECEQ_SUCC, predDecEqSucc.toString());

    }

    private Taclet get(String name, Collection<Taclet> taclets) {
        var n = new Name(name);
        var t = taclets.stream().filter(it -> n.equals(it.name())).findAny().orElse(null);
        Assertions.assertNotNull(t);
        return t;
    }
}
