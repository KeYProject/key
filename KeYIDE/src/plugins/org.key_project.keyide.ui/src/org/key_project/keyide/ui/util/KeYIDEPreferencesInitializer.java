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

package org.key_project.keyide.ui.util;

import org.eclipse.core.runtime.preferences.AbstractPreferenceInitializer;
import org.eclipse.jface.dialogs.MessageDialogWithToggle;
import org.eclipse.swt.graphics.RGB;
import org.key_project.util.java.ColorUtil;

import de.uka.ilkd.key.gui.prooftree.ProofTreeView;

/**
 * Initializes the preferences of {@link KeYIDEPreferences} when they are
 * accessed the first time. This is managed by extension point
 * {@code org.eclipse.core.runtime.preferences}.
 * @author Marco Drebing, Niklas Bunzel, Christoph Schneider, Stefan Käsdorf
 * @see KeYIDEPreferences
 */
public class KeYIDEPreferencesInitializer extends AbstractPreferenceInitializer {
   /**
    * {@inheritDoc}
    */
   @Override
   public void initializeDefaultPreferences() {
      KeYIDEPreferences.setDefaultSwitchToKeyPerspective(MessageDialogWithToggle.PROMPT);
      KeYIDEPreferences.setDefaultClosedGoalColor(ColorUtil.toRGB(ProofTreeView.DARK_GREEN_COLOR));
      KeYIDEPreferences.setDefaultLinkedGoalColor(ColorUtil.toRGB(ProofTreeView.PINK_COLOR));
      KeYIDEPreferences.setDefaultDisabledGoalColor(new RGB(87, 87, 87)); // ColorUtil.toRGB(ProofTreeView.ORANGE_COLOR)
      KeYIDEPreferences.setDefaultOpenGoalColor(ColorUtil.toRGB(ProofTreeView.DARK_RED_COLOR));
      KeYIDEPreferences.setDefaultNodeWithNotesColor(ColorUtil.toRGB(ProofTreeView.ORANGE_COLOR));
      KeYIDEPreferences.setDefaultNodeWithActiveStatementColor(new RGB(0, 0, 255)); // ColorUtil.toRGB(ProofTreeView.LIGHT_BLUE_COLOR)
      KeYIDEPreferences.setDefaultFoundNodeColor(new RGB(168, 211, 255)); // Light blue
   }
}