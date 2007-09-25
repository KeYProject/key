// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.casetool.patternimplementor;

import javax.swing.tree.DefaultMutableTreeNode;

public class PMTreeNode extends DefaultMutableTreeNode {

    private Class pattern;

    private String pmPath;

    PMTreeNode(Class pattern) {
        try {
            this.pmPath = ((AbstractPatternImplementor) pattern.newInstance())
                    .getName();
        } catch (Exception e) {
            e.printStackTrace();
        }

        this.pattern = pattern;
    }

    public Class getPattern() {
        return pattern;
    }

    public String getpmPath() {
        return pmPath;
    }

    public String toString() {
        String retval = pmPath.substring(pmPath.lastIndexOf(":") + 1, pmPath
                .length());

        return retval;
    }
}
