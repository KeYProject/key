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

package org.key_project.shellutility.ui.wizard.page;

import org.eclipse.jface.wizard.WizardPage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.ModifyEvent;
import org.eclipse.swt.events.ModifyListener;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.layout.RowLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swt.widgets.Text;
import org.key_project.util.eclipse.swt.IntegerVerifyListener;
import org.key_project.util.java.StringUtil;

/**
 * Allows to define size and location.
 * @author Martin Hentschel
 */
public class UpdateSizeAndLocationWizardPage extends WizardPage {
   /**
    * The {@link Shell} to update.
    */
   private final Shell shellToUpdate;
   
   /**
    * {@link Text} to define width value.
    */
   private Text sizeWidthText;

   /**
    * {@link Text} to define height value.
    */
   private Text sizeHeightText;

   /**
    * Place shell top left.
    */
   private Button topLeftButton;

   /**
    * Place shell top right.
    */
   private Button topRightButton;

   /**
    * Place shell bottom left.
    */
   private Button bottomLeftButton;

   /**
    * Place shell bottom right.
    */
   private Button bottomRightButton;

   /**
    * Place shell at custom location defined via {@link #locationXText} and {@link #locationYText}.
    */
   private Button customButton;
   
   /**
    * {@link Text} to define x value.
    */
   private Text locationXText;

   /**
    * {@link Text} to define y value.
    */
   private Text locationYText;
   
   /**
    * Constructor.
    * @param pageName The name of this page.
    */
   public UpdateSizeAndLocationWizardPage(String pageName, Shell shellToUpdate) {
      super(pageName);
      this.shellToUpdate = shellToUpdate;
      setTitle("Update Size and Location");
      setDescription("Define size and location to set.");
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void createControl(Composite parent) {
      Composite root = new Composite(parent, SWT.NONE);
      root.setLayout(new GridLayout(1, false));
      setControl(root);
      // screen
      Group screenGroup = new Group(root, SWT.NONE);
      screenGroup.setText("Client Area");
      screenGroup.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      screenGroup.setLayout(new GridLayout(2, false));
      // width
      Label screenWidthLabel = new Label(screenGroup, SWT.NONE);
      screenWidthLabel.setText("Width");
      Text screenWidthText = new Text(screenGroup, SWT.BORDER | SWT.READ_ONLY);
      screenWidthText.setText(parent.getDisplay().getClientArea().width + StringUtil.EMPTY_STRING);
      screenWidthText.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      screenWidthText.addVerifyListener(new IntegerVerifyListener(0, Integer.MAX_VALUE, true));
      // height
      Label screenHeightLabel = new Label(screenGroup, SWT.NONE);
      screenHeightLabel.setText("Height");
      Text screenHeightText = new Text(screenGroup, SWT.BORDER | SWT.READ_ONLY);
      screenHeightText.setText(parent.getDisplay().getClientArea().height + StringUtil.EMPTY_STRING);
      screenHeightText.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      screenHeightText.addVerifyListener(new IntegerVerifyListener(0, Integer.MAX_VALUE, true));      
      // location
      Group locationGroup = new Group(root, SWT.NONE);
      locationGroup.setText("Location");
      locationGroup.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      locationGroup.setLayout(new GridLayout(1, false));
      // Location buttons
      Composite locationButtonsComposite = new Composite(locationGroup, SWT.NONE);
      locationButtonsComposite.setLayout(new RowLayout());
      locationButtonsComposite.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      topLeftButton = new Button(locationButtonsComposite, SWT.RADIO);
      topLeftButton.setText("&Top Left");
      topLeftButton.addSelectionListener(new SelectionAdapter() {
         @Override
         public void widgetSelected(SelectionEvent e) {
            updateCustomLocationEnablement();
            updatePageComplete();
         }
      });
      topRightButton = new Button(locationButtonsComposite, SWT.RADIO);
      topRightButton.setText("T&op Right");
      topRightButton.addSelectionListener(new SelectionAdapter() {
         @Override
         public void widgetSelected(SelectionEvent e) {
            updateCustomLocationEnablement();
            updatePageComplete();
         }
      });
      bottomLeftButton = new Button(locationButtonsComposite, SWT.RADIO);
      bottomLeftButton.setText("&Bottom Left");
      bottomLeftButton.addSelectionListener(new SelectionAdapter() {
         @Override
         public void widgetSelected(SelectionEvent e) {
            updateCustomLocationEnablement();
            updatePageComplete();
         }
      });
      bottomRightButton = new Button(locationButtonsComposite, SWT.RADIO);
      bottomRightButton.setText("Botto&m Right");
      bottomRightButton.addSelectionListener(new SelectionAdapter() {
         @Override
         public void widgetSelected(SelectionEvent e) {
            updateCustomLocationEnablement();
            updatePageComplete();
         }
      });
      customButton = new Button(locationButtonsComposite, SWT.RADIO);
      customButton.setSelection(true);
      customButton.setText("C&ustom");
      customButton.addSelectionListener(new SelectionAdapter() {
         @Override
         public void widgetSelected(SelectionEvent e) {
            updateCustomLocationEnablement();
            updatePageComplete();
         }
      });
      // Custom
      Composite customComposite = new Composite(locationGroup, SWT.NONE);
      customComposite.setLayout(new GridLayout(2, false));
      customComposite.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      // x
      Label locationXLabel = new Label(customComposite, SWT.NONE);
      locationXLabel.setText("&X");
      locationXText = new Text(customComposite, SWT.BORDER);
      locationXText.setText(shellToUpdate.getLocation().x + StringUtil.EMPTY_STRING);
      locationXText.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      locationXText.addVerifyListener(new IntegerVerifyListener(0, Integer.MAX_VALUE, true));
      locationXText.addModifyListener(new ModifyListener() {
         @Override
         public void modifyText(ModifyEvent e) {
            updatePageComplete();
         }
      });
      // y
      Label locationYLabel = new Label(customComposite, SWT.NONE);
      locationYLabel.setText("&Y");
      locationYText = new Text(customComposite, SWT.BORDER);
      locationYText.setText(shellToUpdate.getLocation().y + StringUtil.EMPTY_STRING);
      locationYText.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      locationYText.addVerifyListener(new IntegerVerifyListener(0, Integer.MAX_VALUE, true));
      locationYText.addModifyListener(new ModifyListener() {
         @Override
         public void modifyText(ModifyEvent e) {
            updatePageComplete();
         }
      });
      // size
      Group sizeGroup = new Group(root, SWT.NONE);
      sizeGroup.setText("Size");
      sizeGroup.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      sizeGroup.setLayout(new GridLayout(2, false));
      // width
      Label sizeWidthLabel = new Label(sizeGroup, SWT.NONE);
      sizeWidthLabel.setText("&Width");
      sizeWidthText = new Text(sizeGroup, SWT.BORDER);
      sizeWidthText.setText(shellToUpdate.getSize().x + StringUtil.EMPTY_STRING);
      sizeWidthText.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      sizeWidthText.addVerifyListener(new IntegerVerifyListener(0, Integer.MAX_VALUE, true));
      // height
      Label sizeHeightLabel = new Label(sizeGroup, SWT.NONE);
      sizeHeightLabel.setText("&Height");
      sizeHeightText = new Text(sizeGroup, SWT.BORDER);
      sizeHeightText.setText(shellToUpdate.getSize().y + StringUtil.EMPTY_STRING);
      sizeHeightText.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      sizeHeightText.addVerifyListener(new IntegerVerifyListener(0, Integer.MAX_VALUE, true));
      updateCustomLocationEnablement();
      updatePageComplete();
   }
   
   /**
    * Updates the page complete status.
    */
   protected void updatePageComplete() {
      boolean pageComplete = true;
      if (Location.CUSTOM.equals(getLocation())) {
         if (pageComplete && getX() >= getShell().getDisplay().getClientArea().width) {
            pageComplete = false;
            setErrorMessage("X location is outside of the client area. Maximal value is " + (getShell().getDisplay().getClientArea().width - 1) + ".");
         }
         if (pageComplete && getY() >= getShell().getDisplay().getClientArea().height) {
            pageComplete = false;
            setErrorMessage("Y location is outside of the client area. Maximal value is " + (getShell().getDisplay().getClientArea().height - 1) + ".");
         }
      }
      setPageComplete(pageComplete);
      if (pageComplete) {
         setErrorMessage(null);
      }
   }

   /**
    * Updates the enablement of {@link #locationXText} and {@link #locationYText}.
    */
   protected void updateCustomLocationEnablement() {
      boolean enabled = customButton.getSelection();
      locationXText.setEnabled(enabled);
      locationYText.setEnabled(enabled);
   }

   /**
    * Returns the define width value.
    * @return The defined width value.
    */
   public int getWidth() {
      return getIntValueFromText(sizeWidthText);
   }
   
   /**
    * Returns the define height value.
    * @return The defined height value.
    */
   public int getHeight() {
      return getIntValueFromText(sizeHeightText);
   }
   
   /**
    * Returns the defined location.
    * @return The defined location.
    */
   public Location getLocation() {
      if (topLeftButton.getSelection()) {
         return Location.TOP_LEFT;
      }
      else if (topRightButton.getSelection()) {
         return Location.TOP_RIGHT;
      }
      else if (bottomLeftButton.getSelection()) {
         return Location.BOTTOM_LEFT;
      }
      else if (bottomRightButton.getSelection()) {
         return Location.BOTTOM_RIGHT;
      }
      else {
         return Location.CUSTOM;
      }
   }
   
   /**
    * Returns the define x value.
    * @return The defined x value.
    */
   public int getX() {
      return getIntValueFromText(locationXText);
   }
   
   /**
    * Returns the define y value.
    * @return The defined y value.
    */
   public int getY() {
      return getIntValueFromText(locationYText);
   }
   
   /**
    * Converts the value of the given {@link Text} into an int value.
    * @param text The {@link Text} to convert its value.
    * @return The int value.
    */
   protected int getIntValueFromText(Text text) {
      String value = text.getText();
      return !StringUtil.isEmpty(value) ? 
             Integer.parseInt(value) :
             0;
   }
   
   /**
    * The defined location.
    * @author Martin Hentschel
    */
   public static enum Location {
      TOP_LEFT,
      TOP_RIGHT,
      BOTTOM_LEFT,
      BOTTOM_RIGHT,
      CUSTOM
   }
}