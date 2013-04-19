/*******************************************************************************
 * Copyright (c) 2013 Karlsruhe Institute of Technology, Germany 
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

package org.key_project.util.eclipse.view.editorInView;

import org.eclipse.ui.services.IDisposable;

/**
 * <p>
 * Classes which implements this interface have a normal enabled state
 * which is available via {@code isEnabled()} and {@code setEnabled(boolean)}
 * or something similar by default.
 * </p>
 * <p>
 * But this interface introduces a second primary (global) enabled state
 * which can be checked via {@link #isGlobalEnabled()} and modified
 * via {@link #setGlobalEnabled(boolean)}. The internal normal enabled state
 * should be only {@code true} if the global state is also {@code true}.
 * Otherwise the normal state must be {@code false}. For this reason it is 
 * required to modify the original get state method, e.g. {@code isEnabled()}.
 * </p>
 * @author Martin Hentschel
 * @see AbstractEditorInViewView.
 */
public interface IGlobalEnablement extends IDisposable {
   /**
    * Checks if global enablement is defined.
    * @return {@code true} global enabled, {@code false} global disabled.
    */
   public boolean isGlobalEnabled();
   
   /**
    * Defines the global enablement state.
    * @param globalEnabled {@code true} global enabled, {@code false} global disabled.
    */
   public void setGlobalEnabled(boolean globalEnabled);
}