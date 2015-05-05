package org.key_project.sed.ui.property;

import org.eclipse.debug.core.model.IValue;
import org.eclipse.debug.core.model.IVariable;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.CLabel;
import org.eclipse.swt.layout.FormAttachment;
import org.eclipse.swt.layout.FormData;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Text;
import org.eclipse.ui.views.properties.tabbed.ITabbedPropertyConstants;
import org.eclipse.ui.views.properties.tabbed.TabbedPropertySheetWidgetFactory;
import org.key_project.sed.ui.util.LogUtil;
import org.key_project.util.eclipse.swt.SWTUtil;
import org.key_project.util.java.StringUtil;

/**
 * This composite provides the content shown in {@link VariablePropertySection}.
 * @author Martin Hentschel
 */
public class VariableTabComposite implements IVariableTabContent {
   /**
    * Shows the name.
    */
   private Text nameText;
   
   /**
    * Shows the declared type.
    */
   private Text declaredTypeText;
   
   /**
    * Shows the value.
    */
   private Text valueText;
   
   /**
    * Shows the actual type.
    */
   private Text actualTypeText;

   /**
    * {@inheritDoc}
    */
   @Override
   public void createComposite(Composite parent, TabbedPropertySheetWidgetFactory factory) {
      int labelWidth = 100;
      
      Composite composite = factory.createFlatFormComposite(parent);

      nameText = factory.createText(composite, StringUtil.EMPTY_STRING);
      nameText.setEditable(false);
      FormData data = new FormData();
      data.left = new FormAttachment(0, labelWidth);
      data.right = new FormAttachment(100, 0);
      data.top = new FormAttachment(0, ITabbedPropertyConstants.VSPACE);
      nameText.setLayoutData(data);

      CLabel nameLabel = factory.createCLabel(composite, "Name:");
      data = new FormData();
      data.left = new FormAttachment(0, 0);
      data.right = new FormAttachment(nameText, -ITabbedPropertyConstants.HSPACE);
      data.top = new FormAttachment(nameText, 0, SWT.CENTER);
      nameLabel.setLayoutData(data);

      declaredTypeText = factory.createText(composite, StringUtil.EMPTY_STRING);
      declaredTypeText.setEditable(false);
      data = new FormData();
      data.left = new FormAttachment(0, labelWidth);
      data.right = new FormAttachment(100, 0);
      data.top = new FormAttachment(nameText, 0, ITabbedPropertyConstants.VSPACE);
      declaredTypeText.setLayoutData(data);
      
      CLabel typeLabel = factory.createCLabel(composite, "Declared Type:");
      data = new FormData();
      data.left = new FormAttachment(0, 0);
      data.right = new FormAttachment(declaredTypeText, -ITabbedPropertyConstants.HSPACE);
      data.top = new FormAttachment(declaredTypeText, 0, SWT.CENTER);
      typeLabel.setLayoutData(data);

      valueText = factory.createText(composite, StringUtil.EMPTY_STRING);
      valueText.setEditable(false);
      data = new FormData();
      data.left = new FormAttachment(0, labelWidth);
      data.right = new FormAttachment(100, 0);
      data.top = new FormAttachment(declaredTypeText, 0, ITabbedPropertyConstants.VSPACE);
      valueText.setLayoutData(data);
      
      CLabel valueLabel = factory.createCLabel(composite, "Value:");
      data = new FormData();
      data.left = new FormAttachment(0, 0);
      data.right = new FormAttachment(valueText, -ITabbedPropertyConstants.HSPACE);
      data.top = new FormAttachment(valueText, 0, SWT.CENTER);
      valueLabel.setLayoutData(data);

      actualTypeText = factory.createText(composite, StringUtil.EMPTY_STRING);
      actualTypeText.setEditable(false);
      data = new FormData();
      data.left = new FormAttachment(0, labelWidth);
      data.right = new FormAttachment(100, 0);
      data.top = new FormAttachment(valueText, 0, ITabbedPropertyConstants.VSPACE);
      actualTypeText.setLayoutData(data);
      
      CLabel actualTypeLabel = factory.createCLabel(composite, "Actual Type:");
      data = new FormData();
      data.left = new FormAttachment(0, 0);
      data.right = new FormAttachment(actualTypeText, -ITabbedPropertyConstants.HSPACE);
      data.top = new FormAttachment(actualTypeText, 0, SWT.CENTER);
      actualTypeLabel.setLayoutData(data);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void updateContent(IVariable variable) {
      String name = null;
      String declaredType = null;
      String value = null;
      String actualType = null;
      try {
         if (variable != null) {
            name = variable.getName();
            declaredType = variable.getReferenceTypeName();
            IValue debugValue = variable.getValue();
            if (debugValue != null) {
               value = debugValue.getValueString();
               actualType = debugValue.getReferenceTypeName();
            }
         }
      }
      catch (Exception e) {
         LogUtil.getLogger().logError(e);
      }
      SWTUtil.setText(nameText, name);
      SWTUtil.setText(declaredTypeText, declaredType);
      SWTUtil.setText(valueText, value);
      SWTUtil.setText(actualTypeText, actualType);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void dispose() {
   }
}
