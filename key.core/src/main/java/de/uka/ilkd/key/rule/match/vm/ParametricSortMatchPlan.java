/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.match.vm;

import java.util.List;

import de.uka.ilkd.key.logic.GenericArgument;
import de.uka.ilkd.key.logic.sort.GenericSort;
import de.uka.ilkd.key.logic.sort.ParametricSortInstance;
import de.uka.ilkd.key.rule.match.vm.instructions.MatchGenericSortInstruction;
import de.uka.ilkd.key.rule.match.vm.instructions.SimilarParametricSortInstruction;

import org.key_project.logic.SyntaxElement;
import org.key_project.logic.Term;
import org.key_project.prover.rules.instantiation.MatchResultInfo;
import org.key_project.prover.rules.matcher.compiler.MatchPlan;
import org.key_project.prover.rules.matcher.vm.MatchProgram;
import org.key_project.prover.rules.matcher.vm.instruction.*;

public final class ParametricSortMatchPlan implements MatchPlan {
    private final MatchPlan similar;
    private final List<MatchPlan> children;

    public ParametricSortMatchPlan(ParametricSortInstance psi) {
        this(new SimilarParametricSortInstruction(psi), psi.getArgs().stream().map(a -> {
            if (a.sort() instanceof ParametricSortInstance s) {
                return new ParametricSortMatchPlan(s);
            } else if (a.sort() instanceof GenericSort gs) {
                return new MatchGenericSortInstruction(gs);
            } else {
                return new MatchIdentityInstruction(a);
            }
        }).toList());
    }

    public ParametricSortMatchPlan(MatchPlan similar, List<MatchPlan> children) {
        this.similar = similar;
        this.children = children;
    }

    @Override
    public void emit(List<VMInstruction> out) {
        out.add(new CheckNodeKindInstruction(ParametricSortInstance.class));
        similar.emit(out);
        out.add(GotoNextInstruction.INSTANCE);
        for (MatchPlan child : children) {
            child.emit(out);
        }
    }

    @Override
    public MatchProgram compile() {
        final MatchProgram headCheck = similar.compile();
        final int n = children.size();
        final MatchProgram[] childMatchers = new MatchProgram[n];
        for (int i = 0; i < n; i++) {
            childMatchers[i] = children.get(i).compile();
        }
        return (element, mc, services) -> {
            if (element instanceof GenericArgument(org.key_project.logic.sort.Sort sort) && sort instanceof ParametricSortInstance psi) element = psi;
            else if (!(element instanceof ParametricSortInstance)) return null;
            MatchResultInfo r = headCheck.match(element, mc, services);
            if (r == null) {
                return null;
            }
            for (int i = 0; i < n; i++) {
                r = childMatchers[i].match(element.getChild(i), r, services);
                if (r == null) {
                    return null;
                }
            }
            return r;
        };

    }
}
