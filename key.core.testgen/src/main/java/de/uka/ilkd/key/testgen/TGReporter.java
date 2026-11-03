/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.testgen;

import de.uka.ilkd.key.testgen.smt.testgen.TGPhase;
import de.uka.ilkd.key.testgen.smt.testgen.TestGenerationLifecycleListener;

import org.jspecify.annotations.Nullable;

/**
 * Reporter for test case generation.
 *
 * @author Alexander Weigl
 * @version 1 (24.05.24)
 */
public record TGReporter(TestGenerationLifecycleListener log) {
    /**
     * Writes a message to the underlying log; a {@code null} message is accepted and handled by
     * the listener ({@link TestGenerationLifecycleListener#writeln(Object, String)}), which
     * ignores it.
     */
    public void writeln(@Nullable String message) {
        log.writeln(this, message);
    }

    public void reportException(Exception e) {
        log.writeException(this, e);
    }

    public void phase(TGPhase phase) {
        log.phase(this, phase);
    }

    public void finish() {
        log.finish(this);
    }
}
