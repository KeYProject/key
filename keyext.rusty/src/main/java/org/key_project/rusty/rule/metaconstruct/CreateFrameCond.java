/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.rule.metaconstruct;

import org.key_project.logic.Name;
import org.key_project.logic.Term;
import org.key_project.rusty.Services;
import org.key_project.rusty.logic.op.AbstractTermTransformer;
import org.key_project.rusty.rule.inst.SVInstantiations;

/**
 * Creates the frame condition (aka "modifiable clause") for the given loop. Also accepts the
 * pre-state update and extracts the symbols from there. New symbols in the pre-state update (like
 * "heap_BeforeLOOP") are added to the namespaces. This is because the update is, for the loop scope
 * invariant taclet, created by a variable condition; new symbols created there are not
 * automatically stored in the proof, or will be generated/stored multiple times.
 *
 * @author Dominic Steinhoefel
 */
public class CreateFrameCond extends AbstractTermTransformer {
    public CreateFrameCond() {
        super(new Name("#createFrameCond"), 1);
    }

    @Override
    public Term transform(Term term, SVInstantiations svInst, Services services) {
        final Term loopFormula = term.sub(0);
        return services.getTermBuilder().tt();
    }
}
