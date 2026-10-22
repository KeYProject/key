/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.java;

import de.uka.ilkd.key.java.ast.expression.Assignment;
import de.uka.ilkd.key.java.ast.expression.BinaryAssignment;

import org.key_project.logic.SyntaxElement;

/**
 *
 * @author Alexander Weigl
 * @version 1 (13.08.26)
 */
public class JavaAstUtils {
    public static boolean isCopyAssignment(SyntaxElement a) {
        return a instanceof Assignment b
                && b.getKind() == BinaryAssignment.BinaryAssignmentKind.COPY;
    }
}
