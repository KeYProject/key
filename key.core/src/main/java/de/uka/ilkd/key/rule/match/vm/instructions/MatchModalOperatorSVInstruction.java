/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.match.vm.instructions;

import java.util.Set;

import de.uka.ilkd.key.logic.op.JModality;
import de.uka.ilkd.key.logic.op.ModalOperatorSV;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

import org.key_project.logic.LogicServices;
import org.key_project.logic.SyntaxElement;
import org.key_project.prover.rules.instantiation.MatchResultInfo;
import org.key_project.prover.rules.matcher.vm.instruction.MatchInstruction;

public final class MatchModalOperatorSVInstruction implements MatchInstruction {

    private final Set<JModality.JavaModalityKind> modalityKinds;
    private final ModalOperatorSV modalitySV;

    public MatchModalOperatorSVInstruction(ModalOperatorSV mod) {
        this.modalitySV = mod;
        this.modalityKinds = modalitySV.getModalities().toSet();
    }

    @Override
    public MatchResultInfo match(SyntaxElement actualElement,
            MatchResultInfo mc, LogicServices services) {
        if (actualElement instanceof JModality.JavaModalityKind kind
                && modalityKinds.contains(kind)) {
            final SVInstantiations instantiations = (SVInstantiations) mc.getInstantiations();
            return mc.setInstantiations(instantiations.add(modalitySV, kind, services));
        } else {
            return null;
        }
    }
}
