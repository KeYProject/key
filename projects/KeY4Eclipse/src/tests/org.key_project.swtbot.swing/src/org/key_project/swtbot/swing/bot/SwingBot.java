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
import java.awt.Window;
import java.util.List;

import javax.swing.JButton;
import javax.swing.JDialog;
import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.JList;
import javax.swing.JMenu;
import javax.swing.JMenuBar;
import javax.swing.JMenuItem;
import javax.swing.JPanel;
import javax.swing.JRadioButton;
import javax.swing.JTabbedPane;
import javax.swing.JTree;
import javax.swing.tree.TreeModel;

import org.eclipse.swtbot.swt.finder.SWTBot;
import org.eclipse.swtbot.swt.finder.waits.WaitForObjectCondition;
import org.hamcrest.Matcher;
import org.key_project.swtbot.swing.bot.finder.finders.ChildrenComponentFinder;
import org.key_project.swtbot.swing.bot.finder.finders.Finder;
import org.key_project.swtbot.swing.bot.finder.finders.MenuFinder;
import org.key_project.swtbot.swing.bot.finder.waits.Conditions;
import org.key_project.swtbot.swing.finder.matchers.ComponentMatcherFactory;


/**
 * <p>
 * This class provides an API to test Java Swing applications with the
 * SWTBot approach.
 * </p>
 * <p>
 * The class structure (attributes, methods, visibilities, ...) is oriented
 * on the implementation of {@link SWTBot}.
 * </p>
 * @author Martin Hentschel
 */
public class SwingBot extends SWTBot {
   /**
    * Constructs a bot.
    */
   public SwingBot() {
      this(new Finder());
   }

   /**
    * Constructs a bot that will match the contents of the given parent {@link Component}.
    * @param parent The given parent {@link Component}.
    */
   public SwingBot(Component parent) {
      this(new Finder(new ChildrenComponentFinder(parent), new MenuFinder()));
   }

   /**
    * Constructs a bot with the given finder.
    * @param finder The {@link Finder} to use.
    */
   public SwingBot(Finder finder) {
      super(finder);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Finder getFinder() {
      return (Finder)super.getFinder();
   }
   
   /**
    * Returns a wrapper for the described element.
    * @param title The title on the {@link JFrame}.
    * @return A wrapper around a {@link JFrame} with the specified title.
    */
   public SwingBotJFrame jFrame(String title) {
      return jFrame(title, 0);
   }

   /**
    * Returns a wrapper for the described element.
    * @param title The title on the {@link JFrame}.
    * @param index The index of the {@link JFrame}, in case there are multiple frames with the same title.
    * @return A wrapper around a {@link JFrame} with the specified index.
    */
   public SwingBotJFrame jFrame(String title, int index) {
      return new SwingBotJFrame(jFrames(title).get(index));
   }
   
   /**
    * Returns all available {@link JFrame}s with the defined title.
    * @param title The title on the {@link JFrame}.
    * @return All available {@link JFrame}s with the specified title.
    */
   @SuppressWarnings({ "rawtypes", "unchecked" })
   public List<JFrame> jFrames(String title) {
      Matcher withTitle = ComponentMatcherFactory.allOf(ComponentMatcherFactory.componentOfType(JFrame.class), ComponentMatcherFactory.withTitle(title), ComponentMatcherFactory.componentVisibility(true));
      WaitForObjectCondition<JFrame> waitForShell = Conditions.waitForFrame(withTitle);
      waitUntilWidgetAppears(waitForShell);
      List<JFrame> allShells = waitForShell.getAllMatches();
      return allShells;
   }
   
   /**
    * Returns a wrapper for the described element.
    * @param title The title on the {@link JDialog}.
    * @return A wrapper around a {@link JDialog} with the specified title.
    */   
   public SwingBotJDialog jDialog(String title) {
      return jDialog(title, 0);
   }

   /**
    * Returns a wrapper for the described element.
    * @param title The title on the {@link JDialog}.
    * @param index The index of the {@link JDialog}, in case there are multiple dialogs with the same title.
    * @return A wrapper around a {@link JDialog} with the specified index.
    */   
   public SwingBotJDialog jDialog(String title, int index) {
      return new SwingBotJDialog(jDialogs(title).get(index));
   }
   
   /**
    * Returns all available {@link JDialog}s with the defined title.
    * @param title The title on the {@link JDialog}.
    * @return All available {@link JDialog}s with the specified title.
    */   
   @SuppressWarnings({ "rawtypes", "unchecked" })
   public List<JDialog> jDialogs(String title) {
      Matcher withTitle = ComponentMatcherFactory.allOf(ComponentMatcherFactory.componentOfType(JDialog.class), ComponentMatcherFactory.withTitle(title), ComponentMatcherFactory.componentVisibility(true));
      WaitForObjectCondition<JDialog> waitForDialog = Conditions.waitForWindow(withTitle);
      waitUntilWidgetAppears(waitForDialog);
      List<JDialog> allDialogs = waitForDialog.getAllMatches();
      return allDialogs;
   }
   
   /**
    * Returns a wrapper for the described element.
    * @param prefix The prefix of the title on the {@link JDialog}.
    * @return A wrapper around a {@link JDialog} with the specified title.
    */   
   public SwingBotJDialog jDialogWithPrefix(String prefix) {
      return jDialogWithPrefix(prefix, 0);
   }

   /**
    * Returns a wrapper for the described element.
    * @param prefix The prefix of the title on the {@link JDialog}.
    * @param index The index of the {@link JDialog}, in case there are multiple dialogs with the same title.
    * @return A wrapper around a {@link JDialog} with the specified index.
    */   
   public SwingBotJDialog jDialogWithPrefix(String prefix, int index) {
      return new SwingBotJDialog(jDialogsWithPrefix(prefix).get(index));
   }
   
   /**
    * Returns all available {@link JDialog}s with the defined title.
    * @param prefix The preifx of the title on the {@link JDialog}.
    * @return All available {@link JDialog}s with the specified title.
    */   
   @SuppressWarnings({ "rawtypes", "unchecked" })
   public List<JDialog> jDialogsWithPrefix(String prefix) {
      Matcher withTitle = ComponentMatcherFactory.allOf(ComponentMatcherFactory.componentOfType(JDialog.class), ComponentMatcherFactory.withStartingTitle(prefix), ComponentMatcherFactory.componentVisibility(true));
      WaitForObjectCondition<JDialog> waitForDialog = Conditions.waitForWindow(withTitle);
      waitUntilWidgetAppears(waitForDialog);
      List<JDialog> allDialogs = waitForDialog.getAllMatches();
      return allDialogs;
   }

   /**
    * Returns a wrapper for the described element.
    * @return A wrapper around the {@link JMenuBar}.
    */
   public SwingBotJMenuBar jMenuBar() {
      return new SwingBotJMenuBar(getFinder(), getFinder().findJMenuBar());
   }
   
   /**
    * Returns a wrapper for the described element.
    * @param text The text on the {@link JButton}.
    * @return A wrapper around a {@link JButton} with the specified text.
    */   
   public SwingBotJButton jButton(String text) {
      return jButton(text, 0);
   }
   
   /**
    * Returns a wrapper for the described element.
    * @param text The text on the {@link JButton}.
    * @param index The index of the {@link JButton}, in case there are multiple buttons with the same text.
    * @return A wrapper around a {@link JButton} with the specified index.
    */      
   @SuppressWarnings({ "rawtypes", "unchecked" })
   public SwingBotJButton jButton(String text, int index) {
      Matcher matcher = ComponentMatcherFactory.allOf(ComponentMatcherFactory.componentOfType(JButton.class), ComponentMatcherFactory.withText(text));
      return new SwingBotJButton((JButton)component(matcher, index));
   }

   /**
    * Returns a wrapper for the described element.
    * @param tooltip The tool tip on the {@link JButton}.
    * @return A wrapper around a {@link JButton} with the specified tool tip.
    */      
   public SwingBotJButton jButtonWithTooltip(String tooltip) {
      return jButtonWithTooltip(tooltip, 0);
   }

   /**
    * Returns a wrapper for the described element.
    * @param tooltip The tool tip on the {@link JButton}.
    * @param index The index of the {@link JButton}, in case there are multiple buttons with the same tool tip.
    * @return A wrapper around a {@link JButton} with the specified index.
    */
   @SuppressWarnings({ "rawtypes", "unchecked" })
   public SwingBotJButton jButtonWithTooltip(String tooltip, int index) {
      Matcher matcher = ComponentMatcherFactory.allOf(ComponentMatcherFactory.componentOfType(JButton.class), ComponentMatcherFactory.withToolTipText(tooltip));
      return new SwingBotJButton((JButton)component(matcher, index));
   }
   
   /**
    * Returns a wrapper for the described element.
    * @param text The text on the {@link JRadioButton}.
    * @return A wrapper around a {@link JRadioButton} with the specified text.
    */   
   public SwingBotJRadioButton jRadioButton(String text) {
      return jRadioButton(text, 0);
   }
   
   /**
    * Returns a wrapper for the described element.
    * @param text The text on the {@link JRadioButton}.
    * @param index The index of the {@link JRadioButton}, in case there are multiple buttons with the same text.
    * @return A wrapper around a {@link JRadioButton} with the specified index.
    */      
   @SuppressWarnings({ "rawtypes", "unchecked" })
   public SwingBotJRadioButton jRadioButton(String text, int index) {
      Matcher matcher = ComponentMatcherFactory.allOf(ComponentMatcherFactory.componentOfType(JRadioButton.class), ComponentMatcherFactory.withText(text));
      return new SwingBotJRadioButton((JRadioButton)component(matcher, index));
   }
   
   /**
    * Returns a wrapper for the described element.
    * @return A wrapper around a {@link JTabbedPane}.
    */   
   public SwingBotJTabbedPane jTabbedPane() {
      return jTabbedPane(0);
   }
   
   /**
    * Returns a wrapper for the described element.
    * @param index The index of the {@link JTabbedPane}, in case there are multiple panes.
    * @return A wrapper around a {@link JTabbedPane} with the specified index.
    */      
   @SuppressWarnings({ "rawtypes", "unchecked" })
   public SwingBotJTabbedPane jTabbedPane(int index) {
      Matcher matcher = ComponentMatcherFactory.allOf(ComponentMatcherFactory.componentOfType(JTabbedPane.class));
      return new SwingBotJTabbedPane((JTabbedPane)component(matcher, index));
   }
   
   /**
    * Returns a wrapper for the described element.
    * @return A wrapper around a {@link JTree} with the specified text.
    */   
   public SwingBotJTree jTree() {
      return jTree(0);
   }
   
   /**
    * Returns a wrapper for the described element.
    * @param index The index of the {@link JTree}, in case there are multiple trees in the parent.
    * @return A wrapper around a {@link JTree} with the specified index.
    */      
   @SuppressWarnings({ "rawtypes", "unchecked" })
   public SwingBotJTree jTree(int index) {
      Matcher matcher = ComponentMatcherFactory.allOf(ComponentMatcherFactory.componentOfType(JTree.class));
      return new SwingBotJTree((JTree)component(matcher, index));
   }
   
   /**
    * Returns a wrapper for the described element.
    * @param treeModelClass The type of the tree model.
    * @return A wrapper around a {@link JTree} with the specified text.
    */   
   public SwingBotJTree jTree(Class<? extends TreeModel> treeModelClass) {
      return jTree(treeModelClass, 0);
   }
   
   /**
    * Returns a wrapper for the described element.
    * @param treeModelClass The type of the tree model.
    * @param index The index of the {@link JTree}, in case there are multiple trees in the parent.
    * @return A wrapper around a {@link JTree} with the specified index.
    */      
   @SuppressWarnings({ "rawtypes", "unchecked" })
   public SwingBotJTree jTree(Class<? extends TreeModel> treeModelClass, int index) {
      Matcher matcher = ComponentMatcherFactory.allOf(ComponentMatcherFactory.componentOfType(JTree.class), ComponentMatcherFactory.treeModelOfType(treeModelClass));
      return new SwingBotJTree((JTree)component(matcher, index));
   }
   
   /**
    * Returns a wrapper for the described element.
    * @return A wrapper around a {@link JLabel}.
    */   
   public SwingBotJLabel jLabel() {
      return jLabel(0);
   }
   
   /**
    * Returns a wrapper for the described element.
    * @param index The index of the {@link JLabel}, in case there are multiple trees in the parent.
    * @return A wrapper around a {@link JLabel}.
    */      
   @SuppressWarnings({ "rawtypes", "unchecked" })
   public SwingBotJLabel jLabel(int index) {
      Matcher matcher = ComponentMatcherFactory.allOf(ComponentMatcherFactory.componentOfType(JLabel.class));
      return new SwingBotJLabel((JLabel)component(matcher, index));
   }
   
   /**
    * Returns a wrapper for the described element.
    * @param text The text on the {@link JLabel}.
    * @return A wrapper around a {@link JLabel} with the specified text.
    */   
   public SwingBotJLabel jLabel(String text) {
      return jLabel(text, 0);
   }
   
   /**
    * Returns a wrapper for the described element.
    * @param text The text on the {@link JLabel}.
    * @param index The index of the {@link JLabel}, in case there are multiple buttons with the same text.
    * @return A wrapper around a {@link JLabel} with the specified index.
    */      
   @SuppressWarnings({ "rawtypes", "unchecked" })
   public SwingBotJLabel jLabel(String text, int index) {
      Matcher matcher = ComponentMatcherFactory.allOf(ComponentMatcherFactory.componentOfType(JLabel.class), ComponentMatcherFactory.withText(text));
      return new SwingBotJLabel((JLabel)component(matcher, index));
   }
   
   /**
    * Returns a wrapper for the described element.
    * @return A wrapper around a {@link JList} with the specified text.
    */   
   public SwingBotJList jList() {
      return jList(0);
   }
   
   /**
    * Returns a wrapper for the described element.
    * @param index The index of the {@link JList}, in case there are multiple trees in the parent.
    * @return A wrapper around a {@link JList} with the specified index.
    */      
   @SuppressWarnings({ "rawtypes", "unchecked" })
   public SwingBotJList jList(int index) {
      Matcher matcher = ComponentMatcherFactory.allOf(ComponentMatcherFactory.componentOfType(JList.class));
      return new SwingBotJList((JList)component(matcher, index));
   }
   
   /**
    * Returns the index'th {@link Component} matching the matcher.
    * @param <T> The type of the {@link Component}.
    * @param matcher The matcher used to match {@link Component}s.
    * @param index The index of the {@link Component} in case there are multiple {@link Component}s.
    * @return The index'th {@link Component} matching the matcher.
    */
   public <T extends Component> T component(Matcher<T> matcher, int index) {
      WaitForObjectCondition<T> waitForWidget = Conditions.waitForComponent(matcher);
      waitUntilWidgetAppears(waitForWidget);
      return waitForWidget.get(index);
   }
   
   /**
    * Returns all available opened {@link Window}s.
    * @return All available {@link JDialog}s with the specified title.
    */   
   @SuppressWarnings({ "rawtypes", "unchecked" })
   public List<Window> windows() {
      Matcher condition = ComponentMatcherFactory.allOf(ComponentMatcherFactory.componentOfType(Window.class), ComponentMatcherFactory.componentVisibility(true));
      WaitForObjectCondition<Window> waitForWidnow = Conditions.waitForWindow(condition);
      waitUntilWidgetAppears(waitForWidnow);
      List<Window> allDialogs = waitForWidnow.getAllMatches();
      return allDialogs;
   }

   /**
    * Creates the {@link AbstractSwingBotComponent} for the given {@link Component}
    * or returns {@code null} if it is not supported.
    * @param finder The {@link Finder} to use.
    * @param c The {@link Component} to create the bot instance for.
    * @return The created {@link AbstractSwingBotComponent} or {@code null} if not supported.
    */
   public static AbstractSwingBotComponent<? extends Component> createBotComponent(Finder finder, Component c) {
      if (c instanceof JButton) {
         return new SwingBotJButton((JButton)c);
      }
      else if (c instanceof JDialog) {
         return new SwingBotJDialog((JDialog)c);
      }
      else if (c instanceof JFrame) {
         return new SwingBotJFrame((JFrame)c);
      }
      else if (c instanceof JList) {
         return new SwingBotJList((JList)c);
      }
      else if (c instanceof JMenu) {
         return new SwingBotJMenu(finder, (JMenu)c);
      }
      else if (c instanceof JMenuBar) {
         return new SwingBotJMenuBar(finder, (JMenuBar)c);
      }
      else if (c instanceof JMenuItem) {
         return new SwingBotJMenuItem((JMenuItem)c);
      }
      else if (c instanceof JPanel) {
         return new SwingBotJPanel((JPanel)c);
      }
      else if (c instanceof JRadioButton) {
         return new SwingBotJRadioButton((JRadioButton)c);
      }
      else if (c instanceof JTabbedPane) {
         return new SwingBotJTabbedPane((JTabbedPane)c);
      }
      else if (c instanceof JTree) {
         return new SwingBotJTree((JTree)c);
      }
      else if (c instanceof JLabel) {
          return new SwingBotJLabel((JLabel)c);
       }
      else {
         return null;
      }
   }
}