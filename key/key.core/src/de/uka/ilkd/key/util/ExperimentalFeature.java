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

package de.uka.ilkd.key.util;


/**
 * Instances of this interface control which features are available to the user.
 *
 * Either {@link #deactivate()} or {@link #activate()} is invoked by the main
 * method of the KeY process.
 *
 * @author bruns
 */
public interface ExperimentalFeature {
    /**
     * Deactivate this feature.
     *
     * Currently this is only called from the main method. In later versions
     * this may be called later during execution.
     *
     * Subsequent calls to active must return <code>false</code>.
     */
    public void deactivate();

    /**
     * (Re-)Activate this feature.
     *
     * Currently this is only called from the main method. In later versions
     * this may be called later during execution.
     *
     * Subsequent calls to active must return <code>true</code>.
     */
    public void activate();

    /**
     * Is this feature active?
     *
     * @return <code>true</code> iff this feature has been activated earlier.
     */
    public boolean active();
}