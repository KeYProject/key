/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.testgen;

import de.uka.ilkd.key.testgen.smt.testgen.TGPhase;
import de.uka.ilkd.key.testgen.smt.testgen.TestGenerationLifecycleListener;

/**
 * @author Alexander Weigl
 * @version 1 (24.05.24)
 */
public record TGReporter(TestGenerationLifecycleListener log) {
    public void writeln(String message) {
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
