// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.visualdebugger;

import de.uka.ilkd.key.java.SourceElement;

/**
 * A breakpoint is attached to exact one occurrence of a {@link SourceElement}
 * in the source code. Breakpoints are either <em>enabled</em> or
 * <em>disabled</em>.
 */
public class Breakpoint {

    /**
     * enables or disables the breakpoint
     */
    private boolean enabled = true;

    /**
     * source code element to which the breakpoint is attached
     */
    private final SourceElementId id;

    /**
     * creates a breakpoint attached to the specified source element
     * 
     * @param id
     *                the SourceElementId identifying uniquely an occurrence of
     *                a SourceElement in the code
     */
    public Breakpoint(SourceElementId id) {
        this.id = id;
    }

    /**
     * the occurrence of the source element in the code to which the breakpoint
     * is attached
     * 
     * @return the {@link SourceElementId} referring to an occurrence of a
     *         source code element
     */
    public SourceElementId getId() {
        return id;
    }

    /**
     * true iff. the breakpoint is enabled
     * 
     * @return true iff. the breakpoint is enabled
     */
    public boolean isEnabled() {
        return enabled;

    }

    /**
     * enables or disables the breakpoint
     * 
     * @param enabled
     *                boolean indicating if the breakpoint has to be enabled or
     *                disabled
     */
    public void setEnabled(boolean enabled) {
        this.enabled = enabled;
    }

    /**
     * toString
     */
    public String toString() {
        return "Statement BP at " + id;
    }
}
