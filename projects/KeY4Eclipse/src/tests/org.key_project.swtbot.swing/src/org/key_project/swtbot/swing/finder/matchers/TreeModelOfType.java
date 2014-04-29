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

package org.key_project.swtbot.swing.finder.matchers;

import java.awt.Component;

import javax.swing.JTree;
import javax.swing.tree.TreeModel;

import org.eclipse.swtbot.swt.finder.matchers.AbstractMatcher;
import org.eclipse.swtbot.swt.finder.matchers.WidgetOfType;
import org.hamcrest.Description;
import org.hamcrest.Factory;
import org.hamcrest.Matcher;

/**
 * <p>
 * Tells if a particular {@link Component} is a {@link JTree} 
 * and has a model of a specified type.
 * </p>
 * <p>
 * The class structure (attributes, methods, visibilities, ...) is oriented
 * on the implementation of {@link WidgetOfType}.
 * </p>
 * @author Martin Hentschel
 */
public class TreeModelOfType<T extends Component> extends AbstractMatcher<T> {
   /**
    * The type of {@link TreeModel} to match.
    */
   private Class<? extends TreeModel>  treeModelType;

   /**
    * Matches a {@link Component} that has the specified tree model type
    * @param treeModelType the type of the {@link TreeModel}.
    */   
   TreeModelOfType(Class<? extends TreeModel> treeModelType) {
      this.treeModelType = treeModelType;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected boolean doMatch(Object obj) {
      if (obj instanceof JTree) {
         return treeModelType.isInstance(((JTree)obj).getModel());
      }
      else {
         return false;
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void describeTo(Description description) {
      description.appendText("tree model of type '").appendText(treeModelType.getSimpleName()).appendText("'");
   }

   /**
    * Matches a {@link Component} that is a {@link JTree} and has a model of the specified type.
    * @param <T> The expected {@link Component} type.
    * @param treeModelType the type of the {@link TreeModel}.
    * @return a matcher.
    */   
   @Factory
   public static <T extends Component> Matcher<T> treeModelOfType(Class<? extends TreeModel> treeModelType) {
      return new TreeModelOfType<T>(treeModelType);
   }
}