/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;

import java.util.List;

/**
 * Represents a configuration file.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * cfile: (ckv)* EOF;
 * }</pre>
 */
@NullMarked
public class ConfigurationFile extends BaseAstNode {
    private final List<CKV> entries;

    public ConfigurationFile(Position position, List<CKV> entries) {
        super(position);
        this.entries = entries;
        for (CKV entry : entries) {
            setChildParent(entry);
        }
    }

    public List<CKV> getEntries() {
        return entries;
    }
}