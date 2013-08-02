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

package org.key_project.swtbot.swing.bot.finder.waits;

import java.awt.Frame;
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
 * An {@link ICondition} that waits for a {@link Frame}.
 * </p>
 * <p>
 * The class structure (attributes, methods, visibilities, ...) is oriented
 * on the implementation of {@link org.eclipse.swtbot.swt.finder.waits.WaitForObjectCondition}.
 * </p>
 * @author Martin Hentschel
 */
public class WaitForFrame<T extends Frame> extends WaitForObjectCondition<T> {
   /**
    * Constructor.
    * @param matcher The matchers to use.
    */
   WaitForFrame(Matcher<T> matcher) {
      super(matcher);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getFailureMessage() {
      return "Could not find JFrame matching: " + matcher;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   @SuppressWarnings("unchecked")
   protected List<T> findMatches() {
      IRunnableWithResult<Frame[]> run = new AbstractRunnableWithResult<Frame[]>() {
         @Override
         public void run() {
            setResult(Frame.getFrames());
         }
      };
      SaveSwingUtil.invokeAndWait(run);
      Frame[] frames = run.getResult();
      ArrayList<T> matchingFrames = new ArrayList<T>();
      for (Frame frame : frames) {
         if (matcher.matches(frame)) {
            matchingFrames.add((T)frame);
         }
      }
      return matchingFrames;
   }
}