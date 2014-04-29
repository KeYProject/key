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

package org.key_project.swtbot.swing.bot.finder.finders;

import java.awt.Component;
import java.awt.Container;
import java.awt.Window;
import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;

import javax.swing.JMenuBar;

import org.eclipse.swtbot.swt.finder.finders.ControlFinder;
import org.hamcrest.Matcher;
import org.key_project.swtbot.swing.util.AbstractRunnableWithResult;
import org.key_project.swtbot.swing.util.IRunnableWithResult;
import org.key_project.swtbot.swing.util.SaveSwingUtil;

/**
 * <p>
 * Finds {@link Component}s matching a particular matcher.
 * </p>
 * <p>
 * The class structure (attributes, methods, visibilities, ...) is oriented
 * on the implementation of {@link ControlFinder}.
 * </p>
 * @author Martin Hentschel
 */
public class ComponentFinder {
   /**
    * Finds the {@link Component}s in the active shell matching the given matcher.
    * @param <T> The type of the found {@link Component}s.
    * @param matcher The matcher used to find {@link Component}s in the active {@link Window}.
    * @return All controls in the active {@link Window} that the matcher matches.
    */
   public <T extends Component> List<T> findComponents(Matcher<T> matcher) {
      return findComponents(null, matcher, true);
   }
   
   /**
    * Finds the {@link Component}s starting with the given parent {@link Component} and uses the given matcher. If recursive is set, it will
    * attempt to find the controls recursively in each child {@link Component} if they exist.
    * @param <T> The type of the found {@link Component}s.
    * @param parentcomponent The parent {@link Component} in which controls should be found.
    * @param matcher The matcher used to match the widgets.
    * @param recursive If the match should be recursive.
    * @return All visible {@link Component}s in the parent {@link Component} that the matcher matches. If recursive is {@code true} then find the {@link Component} within each of the parent {@link Component}s.
    */
   public <T extends Component> List<T> findComponents(Component parentcomponent, Matcher<T> matcher, boolean recursive) {
      return findComponentsInternal(parentcomponent, matcher, recursive);
   }   
   
   /**
    * Finds the {@link Component}s starting with the given parent {@link Component} and uses the given matcher. If recursive is set, it will
    * attempt to find the controls recursively in each child {@link Component} if they exist.
    * @param <T> The type of the found {@link Component}s.
    * @param parentComponent The parent {@link Component} in which controls should be found.
    * @param matcher The matcher used to match the widgets.
    * @param recursive If the match should be recursive.
    * @return All visible {@link Component}s in the parent {@link Component} that the matcher matches. If recursive is {@code true} then find the {@link Component} within each of the parent {@link Component}s.
    */
   @SuppressWarnings("unchecked")
   private <T extends Component> List<T> findComponentsInternal(final Component parentComponent, 
                                                                Matcher<T> matcher, 
                                                                boolean recursive) {
      if ((parentComponent == null))
         return new ArrayList<T>();
      if (!parentComponent.isVisible()) {
         return new ArrayList<T>();
      }
      LinkedHashSet<T> components = new LinkedHashSet<T>();
      if (matcher.matches(parentComponent) && !components.contains(parentComponent))
         try {
            components.add((T)parentComponent);
         } catch (ClassCastException exception) {
            throw new IllegalArgumentException("The specified matcher should only match against is declared type.", exception);
         }
      if (recursive) {
         IRunnableWithResult<Component[]> run = new AbstractRunnableWithResult<Component[]>() {
            @Override
            public void run() {
               setResult(parentComponent instanceof Container ? ((Container)parentComponent).getComponents() : new Component[0]);
            }
         };
         SaveSwingUtil.invokeAndWait(run);
         Component[] children = run.getResult();
         components.addAll(findComponentsInternal(children, matcher, recursive));
      }
      return new ArrayList<T>(components);
   }
   
   /**
    * Finds the controls matching one of the {@link Component}s using the given matcher. This will also go recursively though the
    * {@code Component}s provided.
    * @param <T> The type of the found {@link Component}s.
    * @param components The provided {@link Component}s.
    * @param matcher The matcher used to match the widgets.
    * @param recursive If the match should be recursive.
    * @return All visible {@link Component}s in the children that the matcher matches. If recursive is {@code true} then find the {@link Component}s within each of the {@link Component}.
    */
   private <T extends Component> List<T> findComponentsInternal(Component[] components, Matcher<T> matcher, boolean recursive) {
      LinkedHashSet<T> list = new LinkedHashSet<T>();
      for (Component w : components) {
         list.addAll(findComponentsInternal(w, matcher, recursive));
      }
      return new ArrayList<T>(list);
   }
   
   /**
    * Finds the {@link JMenuBar} of the active {@link Window}.
    * @return The {@link JMenuBar} of the active {@link Window} or {@code null} if it has no one.
    */
   public JMenuBar findJMenuBar() {
      return null;
   }
}