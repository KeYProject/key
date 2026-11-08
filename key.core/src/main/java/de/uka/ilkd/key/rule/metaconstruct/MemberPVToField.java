/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.rule.metaconstruct;

import java.util.Objects;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

import org.key_project.logic.Name;
import org.key_project.logic.op.Function;
import org.key_project.logic.op.Operator;

import org.jspecify.annotations.NullMarked;

@TransformerMeta(name = "#memberPVToField")

@NullMarked
public final class MemberPVToField extends AbstractTermTransformer {

    public MemberPVToField() {
        super(new Name("#memberPVToField"), 1);
    }

    @Override
    public JTerm transform(JTerm term, SVInstantiations svInst, Services services) {
        final HeapLDT heapLDT = Objects.requireNonNull(services.getTypeConverter().getHeapLDT(),
            "no heap LDT");

        Operator op = term.sub(0).op();
        if (op instanceof LocationVariable fieldPV) {
            Function fieldSymbol = heapLDT.getFieldSymbolForPV(fieldPV, services);
            return services.getTermBuilder().func(fieldSymbol);
        } else if (heapLDT.getSortOfSelect(op) != null) {
            return term.sub(0).sub(2);
        } else {
            // unreachable for well-formed terms: op is either a field variable or a select op
            assert false;
            throw new IllegalArgumentException("not a heap location: " + term);
        }
    }
}
