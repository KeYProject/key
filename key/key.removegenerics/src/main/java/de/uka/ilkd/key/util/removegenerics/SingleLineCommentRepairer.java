// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

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