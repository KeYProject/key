/* This file is part of KeY - https://key-project.org
 * KeY is licensed by the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0 */
package de.uka.ilkd.key.nparser.builder;

import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.Token;
import javax.annotation.Nullable;

/**
 * @author Alexander Weigl
 * @version 1 (12/9/19)
 */
public final class BuilderHelpers {
    public static String getPosition(@Nullable ParserRuleContext node) {
        if (node == null)
            return " pos n/a";
        return getPosition(node.start);
    }

    public static String getPosition(@Nullable Token t) {
        return t == null ? " pos n/a"
                : String.format(" %s:%d#%d", t.getInputStream().getSourceName(), t.getLine(),
                        t.getCharPositionInLine());
    }

}
