/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;

import java.util.List;

/**
 * Represents a proof script (list of commands).
 * Corresponds to the grammar rule:
 * <pre>{@code
 * proof_script: (proof_script_command)* EOF;
 * }</pre>
 */
@NullMarked
public class ProofScript extends BaseAstNode {
    private final List<ProofScriptCommand> commands;

    public ProofScript(Position position, List<ProofScriptCommand> commands) {
        super(position);
        this.commands = commands;
        for (ProofScriptCommand cmd : commands) {
            setChildParent(cmd);
        }
    }

    public List<ProofScriptCommand> getCommands() {
        return commands;
    }
}