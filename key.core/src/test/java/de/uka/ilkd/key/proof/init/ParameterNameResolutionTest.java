/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.init;

import java.nio.file.Path;
import java.nio.file.Paths;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;

import org.junit.jupiter.api.Disabled;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;

/**
 * Resolution of method-parameter names that look special to KeY.
 */
class ParameterNameResolutionTest {

    private static void load(String dir) throws Exception {
        Path p = Paths.get(
            ParameterNameResolutionTest.class.getResource(dir).toURI());
        KeYEnvironment<DefaultUserInterfaceControl> env =
            KeYEnvironment.load(p, null, null, null);
        env.dispose();
    }

    /**
     * Regression guard for issue #1119: a method parameter named {@code result} (which can also be
     * referred to via {@code \result}) used to fail with "Name already in namespace: result". This
     * now loads fine; the test guards against a reintroduction.
     */
    @Test
    void parameterNamedResultResolves() {
        assertDoesNotThrow(() -> load("issue1119"));
    }

    /**
     * Issue #329: a JML reference to a parameter whose name ends in {@code _<digits>} (e.g.
     * {@code para_0}) fails with "Cannot resolve 'para_0'". Root cause: {@code VariableNamer}
     * treats the {@code _<digits>} suffix as a uniquification index (see
     * {@code VariableNamer.parseName}/{@code getBasenameAndIndex}), so the literal identifier is
     * never matched. Fixing this touches the variable-naming subsystem, hence disabled until then.
     */
    @Disabled("#329: identifier ending in _<digits> mis-parsed as an index by VariableNamer")
    @Test
    void parameterEndingInUnderscoreDigitResolves() {
        assertDoesNotThrow(() -> load("issue329"));
    }
}
