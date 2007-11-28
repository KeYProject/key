// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.visualdebugger;

public class PCLabel implements Label {
    private int id;

    private boolean looking = false;

    public PCLabel(int i, boolean looking) {
        this.looking = looking;
        id = i;
    }

    public int getId() {
        return id;
    }

    public boolean isLooking() {
        return looking;
    }

    public void setLooking(boolean looking) {
        this.looking = looking;
    }

    public String toString() {
        return "PC(" + id + "," + looking + ")";
    }

}
