/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;

/**
 * Represents a proof script command.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * proof_script_command: simple_ident_dots LPAREN (STRING (COMMA STRING)*)? RPAREN NEWLINE;
 * }</pre>
 */
@NullMarked
public class ProofScriptCommand extends BaseAstNode {
    private final String name;
    private final java.util.List<String> arguments;

    public ProofScriptCommand(Position position, String name, java.util.List<String> arguments) {
        super(position);
        this.name = name;
        this.arguments = arguments;
    }

    public String getName() {
        return name;
    }

    public java.util.List<String> getArguments() {
        return arguments;
    }
}