/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.proof.naming;

import java.nio.file.Path;
import java.util.Objects;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.util.HelperClassForTests;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.condition.EnabledIfSystemProperty;

/** One-off generator for the frozen insertHidden.proof compat resource. Not part of the suite. */
public class GenerateHiddenProofResource {

    @Test
    @EnabledIfSystemProperty(named = "key.naming.generate", matches = "true")
    void generate() throws Exception {
        final Path key = HelperClassForTests.TESTCASE_DIRECTORY.resolve("naming")
                .resolve("hideReinsert.key");
        final KeYEnvironment<?> env = KeYEnvironment.load(JavaProfile.getDefaultInstance(),
            key, null, null, null, true);
        try {
            final Proof proof =
                Objects.requireNonNull(env.getLoadedProof(), "the proof must have been loaded");
            // same steps as TestNamingInvariants.splitAndHide, then apply the hidden taclet
            TestNamingInvariants.splitAndHideForGenerator(proof);
            Goal hideGoal = null;
            for (final Goal g : proof.openGoals()) {
                if (g.node().getLocalIntroducedRules().iterator().hasNext()) {
                    hideGoal = g;
                }
            }
            final Goal hiddenGoal =
                Objects.requireNonNull(hideGoal, "splitAndHide must have left a hidden goal");
            final NoPosTacletApp hidden =
                hiddenGoal.node().getLocalIntroducedRules().iterator().next();
            hiddenGoal.apply(hidden);
            final Path out = Path.of(System.getProperty("key.naming.generate.out"));
            new ProofSaver(proof, out).save();
            System.out.println("GEN saved to " + out + " hiddenName=" + hidden.taclet().name());
        } finally {
            env.dispose();
        }
    }
}
