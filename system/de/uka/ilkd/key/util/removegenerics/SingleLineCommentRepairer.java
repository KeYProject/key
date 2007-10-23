package de.uka.ilkd.key.util.removegenerics;

import java.util.List;

import recoder.convenience.TreeWalker;
import recoder.java.Comment;
import recoder.java.ProgramElement;
import recoder.java.SingleLineComment;
import recoder.java.SourceElement;
import recoder.java.SourceElement.Position;

/**
 * This class has been used to repair a bug in recoder. It can be removed as
 * soon as this bug is solved.
 * 
 * The problem is that sometimes comments do not print a newline in the end,
 * which is ensured by {@link #repairSingleLineComments(ProgramElement)}
 * 
 * TODO remove as soon as recoder is patched
 * 
 * @author MU
 */
public class SingleLineCommentRepairer {

    public static void repairSingleLineComments(ProgramElement programElement) {

        TreeWalker tw = new TreeWalker(programElement);

        while (tw.next()) {
            ProgramElement pe = tw.getProgramElement();
            List<Comment> comments = pe.getComments();
            if (comments != null)
                for (Comment comment : comments) {
                    if (comment instanceof SingleLineComment && comment.isPrefixed()) {
                        SourceElement first = pe.getFirstElement();
                        Position relpos = first.getRelativePosition();
                        if (relpos == null || relpos == Position.UNDEFINED) {
                            relpos = new Position(1, 0);
                        } else if (relpos.getLine() < 1) {
                            relpos.setLine(1);
                        }
                        first.setRelativePosition(relpos);
                    }
                }
        }
    }

}
