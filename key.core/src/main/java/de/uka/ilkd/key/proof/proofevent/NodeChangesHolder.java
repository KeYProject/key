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

package de.uka.ilkd.key.proof.proofevent;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.logic.SequentChangeInfo;


public class NodeChangesHolder {
    public ImmutableList<SequentChangeInfo> scis;

    NodeChangesHolder () {
	this ( ImmutableSLList.<SequentChangeInfo>nil() );
    }

    NodeChangesHolder ( ImmutableList<SequentChangeInfo> p_scis ) {
	scis = p_scis;
    }

    public void addSCI ( SequentChangeInfo p_sci ) {
	scis = scis.prepend ( p_sci );
    }

    public Object clone () {
	return new NodeChangesHolder ( scis );
    }
}