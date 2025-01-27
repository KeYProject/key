/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast;

import org.key_project.rusty.ast.expr.FunctionFrame;
import org.key_project.rusty.logic.PossibleProgramPrefix;

public class ProgramPrefixUtil {
    public record ProgramPrefixInfo(int length, FunctionFrame innermostFunctionFrame) {
    }

    public static ProgramPrefixInfo computeEssentials(PossibleProgramPrefix prefix) {
        int length = 1;
        FunctionFrame innermostFunctionFrame = (prefix instanceof FunctionFrame ff ? ff : null);
        while (prefix.hasNextPrefixElement()) {
            prefix = prefix.getNextPrefixElement();
            if (prefix instanceof FunctionFrame ff) {
                innermostFunctionFrame = ff;
            }
            if (!prefix.isPrefix())
                break;
            length++;
        }
        return new ProgramPrefixUtil.ProgramPrefixInfo(length, innermostFunctionFrame);
    }

}
