/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.match.vm.instructions;

import de.uka.ilkd.key.java.ast.reference.SchemaTypeReference;
import de.uka.ilkd.key.java.ast.reference.TypeReference;

import org.key_project.logic.LogicServices;
import org.key_project.logic.SyntaxElement;
import org.key_project.prover.rules.instantiation.MatchResultInfo;
import org.key_project.prover.rules.matcher.vm.instruction.MatchInstruction;

import org.jspecify.annotations.Nullable;

/**
 * Matches a {@link SchemaTypeReference} against the source element, replicating
 * {@code SchemaTypeReference.match}: the source matches iff it is a {@link TypeReference} with the
 * same simple name ({@code getName()}) and the same number of dimensions. It matches any concrete
 * type reference by name; it descends into no prefix and binds no schema variable. As for the
 * other single-position program instructions the cursor advance is the emitted {@code
 * gotoNextSibling}.
 */
public final class MatchSchemaTypeReferenceInstruction implements MatchInstruction {

    private final SchemaTypeReference pattern;

    public MatchSchemaTypeReferenceInstruction(SchemaTypeReference pattern) {
        this.pattern = pattern;
    }

    @Override
    public @Nullable MatchResultInfo match(SyntaxElement actualElement,
            MatchResultInfo matchConditions, LogicServices services) {
        if (actualElement instanceof TypeReference tr
                && pattern.getName().equals(tr.getName())
                && tr.getDimensions() == pattern.getDimensions()) {
            return matchConditions;
        }
        return null;
    }
}
