// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.visualdebugger.executiontree;

import java.util.LinkedList;

import de.uka.ilkd.key.logic.ListOfTerm;
import de.uka.ilkd.key.visualdebugger.SourceElementId;

/**
 * FIXME: the copy method creates insane trees (I do currently no understand
 * what ITNodes are, but most probably the copy method brings ETNodes and
 * ITNodes out of sync), up to now I am not sure which behaviour of copy has
 * been wanted. This bug applies to all subclasses as well.
 */
public class ETStatementNode extends ETNode {
    SourceElementId statementId;

    public ETStatementNode(ListOfTerm bc, LinkedList nodes, SourceElementId id,
            ETNode parent) {
        super(bc, nodes, parent);
        statementId = id;
        assert (id != null);
    }

    public ETStatementNode(ListOfTerm bc, SourceElementId id, ETNode parent) {
        super(bc, parent);
        statementId = id;
        assert (id != null);
    }

    public SourceElementId getStatementId() {
        return statementId;
    }

    public ETNode copy(ETNode p) {
        ETStatementNode copy = new ETStatementNode(getBC(),
                (LinkedList) getITNodes().clone(), statementId, p);
        copy.setChildren((LinkedList) getChildrenList().clone());
        return copy;
    }

    public String print() {

        return super.print() + " " + statementId;
    }

}
