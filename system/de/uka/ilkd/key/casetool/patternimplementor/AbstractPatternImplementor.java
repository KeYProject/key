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

public interface AbstractPatternImplementor {

    /**
     * creates the parameter-structure
     */

    //public abstract void createParameters();
    /**
     * returns the sourcecode of the pattern given the parameters
     */
    public abstract SourceCode getImplementation();

    /**
     * returns the parameters so the gui could be built <code>
     *         JDialog jd = new JDialog();
     *        jd.setContentPane(new PIParameterGUIGroup(patternImplementor.getParameters()));
     *        jd.pack();
     *        jd.setVisible(true);
     * </code>
     */
    public abstract PIParameterGroup getParameters();

    public abstract String getName();
}
