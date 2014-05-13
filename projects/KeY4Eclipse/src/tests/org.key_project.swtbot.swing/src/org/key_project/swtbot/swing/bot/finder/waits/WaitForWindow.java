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

package org.key_project.swtbot.swing.bot.finder.waits;

import java.awt.Window;
import java.util.ArrayList;
import java.util.List;

import org.eclipse.swtbot.swt.finder.waits.ICondition;
import org.eclipse.swtbot.swt.finder.waits.WaitForObjectCondition;
import org.hamcrest.Matcher;
import org.key_project.swtbot.swing.util.AbstractRunnableWithResult;
import org.key_project.swtbot.swing.util.IRunnableWithResult;
import org.key_project.swtbot.swing.util.SaveSwingUtil;

/**
 * <p>
 * An {@link ICondition} that waits for a {@link Window}.
 * </p>
 * <p>
 * The class structure (attributes, methods, visibilities, ...) is oriented
 * on the implementation of {@link org.eclipse.swtbot.swt.finder.waits.WaitForShell}.
 * </p>
 * @author Martin Hentschel
 */
public class WaitForWindow<T extends Window> extends WaitForObjectCondition<T> {
   /**
    * Constructor.
    * @param matcher The matchers to use.
    */
   WaitForWindow(Matcher<T> matcher) {
      super(matcher);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getFailureMessage() {
      return "Could not find Window matching: " + matcher;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   @SuppressWarnings("unchecked")
   protected List<T> findMatches() {
      IRunnableWithResult<Window[]> run = new AbstractRunnableWithResult<Window[]>() {
         @Override
         public void run() {
            setResult(Window.getWindows());
         }
      };
      SaveSwingUtil.invokeAndWait(run);
      Window[] windows = run.getResult();
      ArrayList<T> matchingFrames = new ArrayList<T>();
      for (Window window : windows) {
         if (matcher.matches(window)) {
            matchingFrames.add((T)window);
         }
      }
      return matchingFrames;
   }
}