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

package org.key_project.swtbot.swing.bot;

import java.awt.Component;

import javax.swing.JTree;
import javax.swing.tree.TreeModel;
import javax.swing.tree.TreePath;

import org.eclipse.swtbot.swt.finder.exceptions.WidgetNotFoundException;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTree;
import org.key_project.swtbot.swing.util.AbstractRunnableWithResult;
import org.key_project.swtbot.swing.util.IRunnableWithResult;
import org.key_project.swtbot.swing.util.SaveSwingUtil;

/**
 * <p>
 * This represents a {@link JTree} {@link Component}.
 * </p>
 * <p>
 * The class structure (attributes, methods, visibilities, ...) is oriented
 * on the implementation of {@link SWTBotTree}.
 * </p>
 * @author Martin Hentschel
 */
public class SwingBotJTree extends AbstractSwingBotComponent<JTree> {
   /**
    * Constructs an instance of this object with the given {@link JTree}.
    * @param component The given {@link JTree}.
    * @throws WidgetNotFoundException Is thrown when the given {@link Component} is {@code null}.
    */      
   public SwingBotJTree(JTree component) throws WidgetNotFoundException {
      super(component);
   }
   
   /**
    * Returns the model of the tree.
    * @return The tree model.
    */
   public TreeModel getModel() {
      IRunnableWithResult<TreeModel> run = new AbstractRunnableWithResult<TreeModel>() {
         @Override
         public void run() {
            setResult(component.getModel());
         }
      };
      SaveSwingUtil.invokeAndWait(run);
      return run.getResult();
   }
   
   /**
    * Returns the selected {@link Object}s.
    * @return The selected {@link Object}s.
    */
   public Object[] getSelectedObjects() {
      IRunnableWithResult<Object[]> run = new AbstractRunnableWithResult<Object[]>() {
         @Override
         public void run() {
            TreePath[] selection = component.getSelectionPaths();
            if (selection != null) {
               Object[] result = new Object[selection.length];
               for (int i = 0; i < selection.length; i++) {
                  result[i] = selection[i].getLastPathComponent();
               }
               setResult(result);
            }
            else {
               setResult(new Object[0]);
            }
         }
      };
      SaveSwingUtil.invokeAndWait(run);
      return run.getResult();
   }
   
   /**
    * Deselects all elements in the tree.
    */
   public void unselectAll() {
      SaveSwingUtil.invokeAndWait(new Runnable() {
         @Override
         public void run() {
            component.setSelectionRows(new int[0]);
         }
      });
   }
}