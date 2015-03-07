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

package org.key_project.sed.key.ui.detailFactories;

import java.util.HashSet;
import java.util.Set;

import org.eclipse.debug.internal.ui.views.variables.details.DetailPaneManager;
import org.eclipse.debug.ui.IDetailPane;
import org.eclipse.debug.ui.IDetailPaneFactory;
import org.eclipse.jdt.internal.debug.ui.breakpoints.StandardBreakpointDetailPane;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.key_project.sed.key.core.breakpoints.KeYWatchpoint;
import org.key_project.sed.key.ui.detailPanes.KeYWatchpointDetailPane;

/**
 * This class is responsible to create the correct DetailPane when a KeY Watchpoint is selected in the Breakpoints View.
 * 
 * @author Marco Drebing
 */
@SuppressWarnings("restriction")
public class WatchpointDetailPaneFactory implements IDetailPaneFactory {

   @SuppressWarnings({ "rawtypes", "unchecked" })
   @Override
   public Set getDetailPaneTypes(IStructuredSelection selection) {
      Set result = new HashSet();
      if(selection.getFirstElement() instanceof KeYWatchpoint){
         Set possibleDetailsAreaIDs = new HashSet();
         possibleDetailsAreaIDs.add(StandardBreakpointDetailPane.DETAIL_PANE_STANDARD);
         possibleDetailsAreaIDs.add(KeYWatchpointDetailPane.DETAIL_PANE_KEY_WATCHPOINT);
         DetailPaneManager.getDefault().setPreferredDetailPane(possibleDetailsAreaIDs, KeYWatchpointDetailPane.DETAIL_PANE_KEY_WATCHPOINT);
         result.add(KeYWatchpointDetailPane.DETAIL_PANE_KEY_WATCHPOINT);
         return result;
      }
      return new HashSet();
   }

   @Override
   public String getDefaultDetailPane(IStructuredSelection selection) {
      return KeYWatchpointDetailPane.DETAIL_PANE_KEY_WATCHPOINT;
   }

   @Override
   public IDetailPane createDetailPane(String paneID) {
      if(paneID.equals(KeYWatchpointDetailPane.DETAIL_PANE_KEY_WATCHPOINT))
      return new KeYWatchpointDetailPane();
      return null;
   }

   @Override
   public String getDetailPaneName(String paneID) {
      return "KeY Watchpoint";
   }

   @Override
   public String getDetailPaneDescription(String paneID) {
      if(paneID.equals(KeYWatchpointDetailPane.DETAIL_PANE_KEY_WATCHPOINT))
         return "KeY Watchpoint";
         return null;
   }

}