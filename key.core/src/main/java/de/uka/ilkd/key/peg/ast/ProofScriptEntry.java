/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * Represents a proof script entry (either a reference to an external script or an inline script).
 * Corresponds to the grammar rule:
 * <pre>{@code
 * proof_script_entry: string | LBRACE proof_script RBRACE;
 * }</pre>
 */
@NullMarked
public class ProofScriptEntry extends BaseAstNode {
    private final @Nullable String scriptPath;
    private final @Nullable ProofScript inlineScript;

    public ProofScriptEntry(Position position,
                            @Nullable String scriptPath, @Nullable ProofScript inlineScript) {
        super(position);
        this.scriptPath = scriptPath;
        this.inlineScript = inlineScript;
        setChildParent(inlineScript);
    }

    public @Nullable String getScriptPath() {
        return scriptPath;
    }

    public @Nullable ProofScript getInlineScript() {
        return inlineScript;
    }

    @Override
    public <T> T accept(AstVisitor<T> visitor) {
        return visitor.visit(this);
    }
}