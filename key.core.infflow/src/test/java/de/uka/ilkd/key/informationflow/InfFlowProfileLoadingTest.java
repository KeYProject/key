/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.informationflow;

import java.nio.file.Path;
import java.util.Objects;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.nparser.KeyAst;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.AbstractProfile;
import de.uka.ilkd.key.scripts.ProofScriptEngine;

import org.key_project.util.helper.FindResources;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Regression tests for the profile resolution of the problem loader.
 * <p>
 * Information flow problem files declare {@code \profile "java-infflow"}. When the loader was
 * given a (default) profile with {@code forceNewProfileOfNewProofs = false}, that profile
 * nevertheless overrode the file's declaration. Under the plain Java profile the auxiliary
 * computation of the information flow macros uses the ordinary "Use Operation Contract" rule
 * instead of "InfFlow Use Operation Contract", loses the RELATED_BY_* tracking and the proof can
 * no longer be closed. This is how the GUI (examples dialog, recent files) and the command line
 * loaded every file, so infflow proofs closed headlessly (e.g. in RunAllProofs) but not
 * interactively.
 */
public class InfFlowProfileLoadingTest {
    private static final String EXAMPLE = "InformationFlow/NewObjects/"
        + "object.AmtoftBanerjee(object.AmtoftBanerjee__m_1()).Non-interference contract.0.m.key";

    private static Path exampleFile() {
        return Objects.requireNonNull(FindResources.getExampleDirectory()).resolve(EXAMPLE);
    }

    /**
     * A default profile passed without force (as the GUI's problem loader does) must not override
     * the file's {@code \profile} declaration.
     */
    @Test
    void unforcedProfileDefersToFileDeclaration() throws Exception {
        KeYEnvironment<DefaultUserInterfaceControl> env = KeYEnvironment.load(
            AbstractProfile.getDefaultProfile(), exampleFile(), null, null, null, false);
        try {
            assertEquals(JavaInfFlowProfile.PROFILE_ID,
                env.getLoadedProof().getServices().getProfile().ident(),
                "the file's \\profile declaration must win over an unforced profile");
        } finally {
            env.dispose();
        }
    }

    /**
     * With {@code forceNewProfileOfNewProofs = true} the passed profile wins over the file's
     * declaration (used e.g. when the user explicitly picks a profile in the file chooser).
     */
    @Test
    void forcedProfileOverridesFileDeclaration() throws Exception {
        KeYEnvironment<DefaultUserInterfaceControl> env = KeYEnvironment.load(
            AbstractProfile.getDefaultProfile(), exampleFile(), null, null, null, true);
        try {
            assertEquals(AbstractProfile.getDefaultProfile().ident(),
                env.getLoadedProof().getServices().getProfile().ident(),
                "a forced profile must override the file's \\profile declaration");
        } finally {
            env.dispose();
        }
    }

    /**
     * End-to-end guard: loaded with the (previously broken) unforced default profile, the
     * embedded infflow-autopilot script must close the proof. Before the fix this got stuck with
     * an open goal after ~25 nodes because the auxiliary computation ran under the wrong profile.
     */
    @Test
    void autopilotClosesProofWhenLoadedLikeTheGui() throws Exception {
        KeYEnvironment<DefaultUserInterfaceControl> env = KeYEnvironment.load(
            AbstractProfile.getDefaultProfile(), exampleFile(), null, null, null, false);
        try {
            Proof proof = env.getLoadedProof();
            KeyAst.ProofScript script = env.getProofScript();
            assertNotNull(script, "expected embedded \\proofScript in .m.key file");

            new ProofScriptEngine(proof).execute(env.getUi(), script);

            assertTrue(proof.closed(), "proof should close via the infflow-autopilot script");
        } finally {
            env.dispose();
        }
    }
}
