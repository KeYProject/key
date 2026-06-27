/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;

/**
 * Base interface for all declaration types in KeY specification files.
 *
 * @author Cline
 * @version 1.0
 */
@NullMarked
public interface Declaration extends AstNode {
    // Marker interface for all declarations
}