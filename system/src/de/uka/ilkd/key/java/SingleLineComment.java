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

package de.uka.ilkd.key.java;

/** Any non-SingleLineComment is a multi line comment. */

public class SingleLineComment extends Comment {

    /**
     Single line comment.
     */

    public SingleLineComment() {}

    /**
     Single line comment.
     @param text a string.
     */

    public SingleLineComment(String text) {
        super(text);
    }
}