package de.uka.ilkd.key.java;

import de.uka.ilkd.key.java.ast.expression.Assignment;
import org.key_project.logic.SyntaxElement;

/**
 *
 * @author Alexander Weigl
 * @version 1 (13.08.26)
 */
public class JavaAstUtils {
    public static boolean isCopyAssignment(SyntaxElement a) {
        return a instanceof Assignment b && b.getKind() == Assignment.AssignmentKind.COPY;
    }
}
