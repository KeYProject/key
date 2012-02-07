/*******************************************************************************
 * Copyright (c) 2011 Martin Hentschel.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Martin Hentschel - initial API and implementation
 *******************************************************************************/

package de.hentschel.visualdbc.generation.ui.test.util;

import org.eclipse.swtbot.swt.finder.widgets.SWTBotShell;

/**
 * Implementations of this interface manipulates the values in a {@link SWTBotShell}.
 * @author Martin Hentschel
 */
public interface ISWTBotShellManipulator {
   /**
    * Manipulates the shell values.
    * @param shell The shell to manipulate.
    */
   public void manipulate(SWTBotShell shell);
}
