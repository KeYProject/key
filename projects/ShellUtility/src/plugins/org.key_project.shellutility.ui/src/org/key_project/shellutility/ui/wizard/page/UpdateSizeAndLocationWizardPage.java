package org.key_project.shellutility.ui.wizard.page;

import org.eclipse.jface.wizard.WizardPage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Text;
import org.key_project.util.eclipse.swt.IntegerVerifyListener;
import org.key_project.util.java.StringUtil;

/**
 * Allows to define size and location.
 * @author Martin Hentschel
 */
public class UpdateSizeAndLocationWizardPage extends WizardPage {
   /**
    * {@link Text} to define width value.
    */
   private Text sizeWidthText;

   /**
    * {@link Text} to define height value.
    */
   private Text sizeHeightText;

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
   public UpdateSizeAndLocationWizardPage(String pageName) {
      super(pageName);
      setTitle("Update Size and Location");
      setDescription("Define size and location to set.");
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void createControl(Composite parent) {
      Composite root = new Composite(parent, SWT.NONE);
      root.setLayout(new GridLayout(2, false));
      setControl(root);
      // width
      Label sizeWidthLabel = new Label(root, SWT.NONE);
      sizeWidthLabel.setText("&Width");
      sizeWidthText = new Text(root, SWT.BORDER);
      sizeWidthText.setText("1280");
      sizeWidthText.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      sizeWidthText.addVerifyListener(new IntegerVerifyListener(0, Integer.MAX_VALUE, true));
      // height
      Label sizeHeightLabel = new Label(root, SWT.NONE);
      sizeHeightLabel.setText("&Height");
      sizeHeightText = new Text(root, SWT.BORDER);
      sizeHeightText.setText("720");
      sizeHeightText.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      sizeHeightText.addVerifyListener(new IntegerVerifyListener(0, Integer.MAX_VALUE, true));
      // x
      Label locationXLabel = new Label(root, SWT.NONE);
      locationXLabel.setText("&X");
      locationXText = new Text(root, SWT.BORDER);
      locationXText.setText("0");
      locationXText.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      locationXText.addVerifyListener(new IntegerVerifyListener(0, Integer.MAX_VALUE, true));
      // y
      Label locationYLabel = new Label(root, SWT.NONE);
      locationYLabel.setText("&Y");
      locationYText = new Text(root, SWT.BORDER);
      locationYText.setText("0");
      locationYText.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      locationYText.addVerifyListener(new IntegerVerifyListener(0, Integer.MAX_VALUE, true));
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
}
