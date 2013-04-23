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

package org.key_project.sed.key.ui.launch;

import org.eclipse.jface.window.Window;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.CCombo;
import org.eclipse.swt.custom.CLabel;
import org.eclipse.swt.custom.CTabFolder;
import org.eclipse.swt.custom.CTabItem;
import org.eclipse.swt.custom.ScrolledComposite;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.List;
import org.eclipse.swt.widgets.Table;
import org.eclipse.swt.widgets.Text;
import org.eclipse.swt.widgets.Tree;
import org.eclipse.ui.forms.widgets.ExpandableComposite;
import org.eclipse.ui.forms.widgets.Hyperlink;
import org.eclipse.ui.forms.widgets.ImageHyperlink;
import org.eclipse.ui.views.properties.tabbed.TabbedPropertySheetWidgetFactory;

/**
 * An implementation of {@link TabbedPropertySheetWidgetFactory} which
 * creates instead of widgets for forms normal widgets for the default user interface. 
 * @author Martin Hentschel
 */
public class NoFormTabbedPropertySheetWidgetFactory extends TabbedPropertySheetWidgetFactory {
   /**
    * {@inheritDoc}
    */
   @Override
   public Group createGroup(Composite parent, String text) {
      Group group = new Group(parent, SWT.NONE);
      group.setText(text);
      return group;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Text createText(Composite parent, String value) {
      Text text = new Text(parent, SWT.BORDER);
      if (value != null) {
         text.setText(value);
      }
      return text;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Text createText(Composite parent, String value, int style) {
      Text text = new Text(parent, SWT.BORDER | style);
      if (value != null) {
         text.setText(value);
      }
      return text;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Label createLabel(Composite parent, String text) {
      Label label = new Label(parent, SWT.NONE);
      label.setText(text);
      return label;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Label createLabel(Composite parent, String text, int style) {
      Label label = new Label(parent, style);
      label.setText(text);
      return label;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Button createButton(Composite parent, String text, int style) {
      Button button = new Button(parent, style);
      button.setText(text);
      return button;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Composite createPlainComposite(Composite parent, int style) {
      return new Composite(parent, style);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Composite createFlatFormComposite(Composite parent) {
      return new Composite(parent, SWT.NONE);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public CTabFolder createTabFolder(Composite parent, int style) {
      return new CTabFolder(parent, style);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public CTabItem createTabItem(CTabFolder tabFolder, int style) {
      return new CTabItem(tabFolder, style);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public List createList(Composite parent, int style) {
      return new List(parent, style);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Composite createComposite(Composite parent, int style) {
      return new Composite(parent, style);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Composite createComposite(Composite parent) {
      return new Composite(parent, SWT.NONE);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ScrolledComposite createScrolledComposite(Composite parent, int style) {
      return new ScrolledComposite(parent, style);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public CCombo createCCombo(Composite parent, int comboStyle) {
      return new CCombo(parent, comboStyle);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public CCombo createCCombo(Composite parent) {
      return new CCombo(parent, SWT.NONE);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public CLabel createCLabel(Composite parent, String text) {
      CLabel label = new CLabel(parent, SWT.NONE);
      label.setText(text);
      return label;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public CLabel createCLabel(Composite parent, String text, int style) {
      CLabel label = new CLabel(parent, style);
      label.setText(text);
      return label;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Hyperlink createHyperlink(Composite parent, String text, int style) {
      Hyperlink link = new Hyperlink(parent, style);
      link.setText(text);
      return link;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ImageHyperlink createImageHyperlink(Composite parent, int style) {
      return new ImageHyperlink(parent, style);
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public ExpandableComposite createExpandableComposite(Composite parent, int expansionStyle) {
      return new ExpandableComposite(parent, expansionStyle);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Label createSeparator(Composite parent, int style) {
      return new Label(parent, SWT.SEPARATOR | style | Window.getDefaultOrientation());
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Table createTable(Composite parent, int style) {
      return new Table(parent, style);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Tree createTree(Composite parent, int style) {
      return new Tree(parent, style);
   }
}