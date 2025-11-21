/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.testgen.smt.testgen;

import org.jspecify.annotations.Nullable;

/**
 *
 */
public interface TestGenerationLifecycleListener {
    void phase(Object sender, TGPhase phase);

    void writeln(Object sender, @Nullable String message);

    void writeException(Object sender, Throwable throwable);

    void finish(Object sender);
}
