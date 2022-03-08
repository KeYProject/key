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

package de.uka.ilkd.key.java.statement;

import de.uka.ilkd.key.java.Comment;
import de.uka.ilkd.key.java.PositionInfo;
import org.key_project.util.ExtList;

import java.util.List;

public abstract class JumpStatement extends JavaStatement {
    /**
     * Jump statement.
     *
     * @param children the children of this AST element as KeY classes.
     *                 May contain: Comments
     */
    public JumpStatement(ExtList children) {
        super(children);
    }

    public JumpStatement(PositionInfo pi, List<Comment> comments) {
        super(pi, comments);
    }
}