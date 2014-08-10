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

package de.uka.ilkd.key.strategy;

import java.util.Set;

import de.uka.ilkd.key.gui.ApplyStrategy.IStopCondition;
import de.uka.ilkd.key.symbolic_execution.strategy.breakpoint.IBreakpoint;

/**
 * Defines the basic functionality of an {@link IStopCondition} which
 * stops applying rules when at least one {@link IBreakpoint} is hit.
 * @author Martin Hentschel
 */
public interface IBreakpointStopCondition extends IStopCondition {
   /**
    * Adds a new {@link IBreakpoint}.
    * @param breakpoint The {@link IBreakpoint} to add.
    */
   public void addBreakpoint(IBreakpoint breakpoint);
   
   /**
    * Removes an {@link IBreakpoint}.
    * @param breakpoint The {@link IBreakpoint} to remove.
    */
   public void removeBreakpoint(IBreakpoint breakpoint);
   
   /**
    * Returns all available {@link IBreakpoint}s.
    * @return The available {@link IBreakpoint}s.
    */
   public Set<IBreakpoint> getBreakpoints();
}