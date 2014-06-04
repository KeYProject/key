/*******************************************************************************
 * Copyright (c) 2014 Karlsruhe Institute of Technology, Germany
 *                    Technical University Darmstadt, Germany
 *                    Chalmers University of Technology, Sweden
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Technical University Darmstadt - initial API and implementation and/or initial documentation
 *******************************************************************************/

package org.key_project.sed.key.ui.detailPanes;

import org.eclipse.jdt.debug.ui.breakpoints.JavaBreakpointConditionEditor;
import org.eclipse.jdt.internal.debug.ui.JDIDebugUIPlugin;
import org.eclipse.jdt.internal.debug.ui.breakpoints.AbstractDetailPane;
import org.eclipse.jdt.internal.debug.ui.breakpoints.AbstractJavaBreakpointEditor;
import org.eclipse.jdt.internal.debug.ui.breakpoints.BreakpointMessages;
import org.eclipse.jdt.internal.debug.ui.breakpoints.CompositeBreakpointEditor;
import org.eclipse.jdt.internal.debug.ui.breakpoints.StandardJavaBreakpointEditor;
import org.eclipse.swt.widgets.Composite;
import org.key_project.sed.key.ui.editors.KeYWatchpointConditionEditor;

/**
 * This class represents a a Detail Pane, which is displayed when a KeY Watchpoint is slected in the Breakpoints View
 * or the Properties of a KeY Watchpoint are edited.
 * 
 * @author Marco Drebing
 */
@SuppressWarnings("restriction")
public class KeYWatchpointDetailPane extends AbstractDetailPane {

   public static final String DETAIL_PANE_KEY_WATCHPOINT = JDIDebugUIPlugin.getUniqueIdentifier() + ".DETAIL_PANE_KEY_WATCHPOINT";
   
   /**
    * Creates a new {@link KeYWatchpointDetailPane}. this pane holds a {@link StandardJavaBreakpointEditor} and a {@link KeYWatchpointConditionEditor}.
    */
   public KeYWatchpointDetailPane() {
      super(BreakpointMessages.BreakpointConditionDetailPane_0, BreakpointMessages.BreakpointConditionDetailPane_0, DETAIL_PANE_KEY_WATCHPOINT); 
      addAutosaveProperties(new int[]{
            JavaBreakpointConditionEditor.PROP_CONDITION_ENABLED,
            JavaBreakpointConditionEditor.PROP_CONDITION_SUSPEND_POLICY});
   }

   @Override
   protected AbstractJavaBreakpointEditor createEditor(Composite parent) {
      return new CompositeBreakpointEditor(
            new AbstractJavaBreakpointEditor[] {new StandardJavaBreakpointEditor(), new KeYWatchpointConditionEditor()});
   }

}