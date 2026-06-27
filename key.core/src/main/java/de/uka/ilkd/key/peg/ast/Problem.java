/* This file is part of KeY - https://project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * Represents a problem declaration in a KeY specification file.
 * Corresponds to the grammar rule: problem
 *
 * @author Cline
 * @version 1.0
 */
@NullMarked
public class Problem extends BaseAstNode implements Declaration {
    private final @Nullable Term termOrSeq;
    private final @Nullable String chooseContract;
    private final @Nullable String proofObligation;
    private final @Nullable ProofScriptEntry proofScriptEntry;

    public Problem(Position position,
                   @Nullable Term termOrSeq, @Nullable String chooseContract,
                   @Nullable String proofObligation, @Nullable ProofScriptEntry proofScriptEntry) {
        super(position);
        this.termOrSeq = termOrSeq;
        this.chooseContract = chooseContract;
        this.proofObligation = proofObligation;
        this.proofScriptEntry = proofScriptEntry;
        setChildParent(termOrSeq);
        setChildParent(proofScriptEntry);
    }

    @Override
    public <T> T accept(AstVisitor<T> visitor) {
        return visitor.visit(this);
    }

    public @Nullable Term getTermOrSeq() {
        return termOrSeq;
    }

    public @Nullable String getChooseContract() {
        return chooseContract;
    }

    public @Nullable String getProofObligation() {
        return proofObligation;
    }

    public @Nullable ProofScriptEntry getProofScriptEntry() {
        return proofScriptEntry;
    }
}