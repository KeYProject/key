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

import java.awt.Component;
import java.util.List;

import org.eclipse.core.runtime.Assert;
import org.eclipse.swtbot.swt.finder.waits.ICondition;
import org.eclipse.swtbot.swt.finder.waits.WaitForObjectCondition;
import org.hamcrest.Matcher;
import org.key_project.swtbot.swing.bot.finder.finders.Finder;


/**
 * <p>
 * An {@link ICondition} that waits for a {@link Component}.
 * </p>
 * <p>
 * The class structure (attributes, methods, visibilities, ...) is oriented
 * on the implementation of {@link org.eclipse.swtbot.swt.finder.waits.WaitForWidget}.
 * </p>
 * @author Martin Hentschel
 */
public class WaitForComponent<T extends Component> extends WaitForObjectCondition<T> {
   /**
    * Constructor.
    * @param matcher The matchers to use.
    */
   WaitForComponent(Matcher<T> matcher) {
      super(matcher);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getFailureMessage() {
      return "Could not find component matching: " + matcher;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected List<T> findMatches() {
      Assert.isTrue(bot.getFinder() instanceof Finder);
      Finder finder = (Finder)bot.getFinder();
      return finder.findComponents(matcher);
   }
}