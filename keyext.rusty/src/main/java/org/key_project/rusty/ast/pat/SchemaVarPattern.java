/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast.pat;

import org.key_project.logic.SyntaxElement;
import org.key_project.logic.Term;
import org.key_project.rusty.Services;
import org.key_project.rusty.ast.RustyProgramElement;
import org.key_project.rusty.ast.SourceData;
import org.key_project.rusty.ast.visitor.Visitor;
import org.key_project.rusty.logic.op.sv.OperatorSV;
import org.key_project.rusty.rule.MatchConditions;
import org.key_project.rusty.rule.inst.SVInstantiations;

import org.jspecify.annotations.NonNull;

// spotless:off
public record SchemaVarPattern(boolean reference, boolean mut, OperatorSV operatorSV) implements Pattern {
    @Override
    public @NonNull SyntaxElement getChild(int n) {
        if (n == 0) return operatorSV;
        throw new IndexOutOfBoundsException("SchemaVarPattern has only one child");
    }

    @Override
    public int getChildCount() {
        return 1;
    }

    @Override
    public MatchConditions match(SourceData source, MatchConditions mc) {
        final Services services = source.getServices();
        final RustyProgramElement src = source.getSource();

        final SVInstantiations instantiations = mc.getInstantiations();
        final Object instant = instantiations.getInstantiation(operatorSV);
        if (instant == null || instant.equals(src) || (instant instanceof Term t && t.op().equals(src))) {
            mc = addPatternInstantiation(src, mc, instantiations, instant, services);
            if (mc == null) {
                return null;
            }
        } else {
            return null;
        }
        source.next();
        return mc;
    }

    private MatchConditions addPatternInstantiation(RustyProgramElement pe, MatchConditions mc, SVInstantiations insts, Object foundInst, Services services) {
        if (mc == null) {
            return null;
        }

        if (foundInst != null) {
            final Object newInst;
            if (foundInst instanceof Term) {
                newInst = services.convertToLogicElement(pe);
            } else {
                newInst = pe;
            }

            if (foundInst.equals(newInst)) {
                return mc;
            } else {
                return null;
            }
        }

        insts = insts.add(operatorSV, pe, services);
        return insts == null ? null : mc.setInstantiations(insts);
    }

    @Override
    public void visit(Visitor v) {
        v.performActionOnSchemaVarPattern(this);
    }
}
//spotless:on
