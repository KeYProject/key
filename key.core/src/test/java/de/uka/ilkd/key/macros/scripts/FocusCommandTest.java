/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.macros.scripts;

import java.nio.file.Files;
import java.nio.file.Path;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.io.ProofSaver;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * @author Alexander Weigl
 * @version 1 (17.10.19)
 */
public class FocusCommandTest {
    @Test
    public void testSimpleSelection() throws Exception {
        Path temp = Files.createTempFile("key-focus-command", ".key");
        Files.writeString(temp, "\\functions { int i; } \\problem { i=1&i=2 -> i=3|i=4 }" +
            "\\proofScript \"prop-simp; \"");
        KeYEnvironment<DefaultUserInterfaceControl> env = KeYEnvironment.load(temp.toFile());
        Proof p = env.getLoadedProof();
        ProofScriptEngine pse = new ProofScriptEngine(
            "macro 'nosplit-prop'; focus 'i=1 ==> i = 4';",
            new Location(null, Position.newOneBased(1, 1)));
        pse.execute(env.getUi(), p);

        assertEquals(1, p.openGoals().size());
        Goal g = p.openGoals().head();
        assertEquals("i = Z(1(#)) ==> i = Z(4(#))",
            ProofSaver.printAnything(g.sequent(), env.getServices()));
    }

    @Test
    public void testSelectionWithLabels() throws Exception {
        Path temp = Files.createTempFile("key-focus-command", ".key");
        Files.writeString(temp,
            "\\functions { int i; } \\problem { i=1<<SC>> -> i=(3<<origin(\"<none> (implicit)\", \"[]\")>>) }"
                +
                "\\proofScript \"prop-simp; \"");

        KeYEnvironment<DefaultUserInterfaceControl> env = KeYEnvironment.load(temp.toFile());
        Proof p = env.getLoadedProof();
        ProofScriptEngine pse = new ProofScriptEngine(
            "macro 'nosplit-prop'; focus 'i=1 ==> i = 3';",
            new Location(null, Position.newOneBased(1, 1)));
        pse.execute(env.getUi(), p);

        assertEquals(1, p.openGoals().size());
        Goal g = p.openGoals().head();
        assertEquals("i = Z(1(#))<<SC>> ==> i = Z(3(#))",
            ProofSaver.printAnything(g.sequent(), env.getServices()));
    }

}
