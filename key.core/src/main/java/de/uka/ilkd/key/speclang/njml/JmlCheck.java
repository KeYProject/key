/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang.njml;

import java.util.List;
import javax.annotation.Nonnull;

import de.uka.ilkd.key.speclang.PositionedString;

import org.antlr.v4.runtime.ParserRuleContext;

/**
 * Interface describes a syntactical check on JML parse trees.
 *
 * @author Alexander Weigl
 * @version 1 (6/8/21)
 */
public interface JmlCheck {
    /**
     * Checks for the given parse tree and returns warnings if necessary.
     *
     * @param ctx an arbitrary {@link ParserRuleContext} from the {@link JmlParser}
     * @return a potential empty list of warnings
     */
    @Nonnull
    List<PositionedString> check(@Nonnull ParserRuleContext ctx);
}
