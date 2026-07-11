/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.match.vm;

import de.uka.ilkd.key.rule.MatchConditions;

import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.prover.rules.instantiation.MatchResultInfo;
import org.key_project.prover.rules.matcher.compiler.BinderMatcher;
import org.key_project.prover.rules.matcher.vm.instruction.MatchInstruction;
import org.key_project.util.collection.ImmutableArray;

import static de.uka.ilkd.key.rule.match.vm.instructions.JavaDLMatchVMInstructionSet.matchAndBindVariables;

/**
 * Java-DL implementation of the {@link BinderMatcher} SPI: bound variables are bound via the
 * {@code matchAndBindVariables} instruction, and the binding scope is closed via
 * {@link MatchConditions#shrinkRenameTable()}. The renaming table is scope-structured — closing
 * pops one scope — so the bound variables themselves are not needed for unbinding.
 */
public final class JavaBinderMatcher implements BinderMatcher {

    /** stateless; a single shared instance suffices. */
    public static final JavaBinderMatcher INSTANCE = new JavaBinderMatcher();

    private JavaBinderMatcher() {}

    @SuppressWarnings("unchecked")
    @Override
    public MatchInstruction binder(ImmutableArray<? extends QuantifiableVariable> boundVars) {
        return matchAndBindVariables((ImmutableArray<QuantifiableVariable>) boundVars);
    }

    @Override
    public MatchResultInfo unbind(MatchResultInfo mc,
            ImmutableArray<? extends QuantifiableVariable> boundVars) {
        return ((MatchConditions) mc).shrinkRenameTable();
    }
}
