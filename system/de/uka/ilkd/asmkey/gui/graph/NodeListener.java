// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.asmkey.gui.graph;

/**
 * A node listener is used in the {@link ArcsComponent}. Classes
 * implementing the interface can be used as listener to implement
 * reactions when the user select, double-click, etc... a node
 * in the {@link ArcsComponent}.
 */
public interface NodeListener {

    void nodeSelected(Node node);

    void nodeDoubleClicked(Node node);

}
