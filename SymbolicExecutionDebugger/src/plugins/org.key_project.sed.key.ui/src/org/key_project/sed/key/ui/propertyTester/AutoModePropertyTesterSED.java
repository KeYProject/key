package org.key_project.sed.key.ui.propertyTester;

import org.eclipse.core.expressions.PropertyTester;
import org.key_project.sed.key.ui.view.ManualView;
import org.key_project.util.eclipse.WorkbenchUtil;

import de.uka.ilkd.key.control.ProofControl;

/**
 * tests the properties that are needed for starting and stopping auto mode.
 * @author Seena Vellaramkalayil
 *
 */
public class AutoModePropertyTesterSED extends PropertyTester {

   public static final String PROPERTY_NAMESPACE = "org.key_project.sed.key.ui";
   
   public static final String PROPERTY_IS_AUTO_MODE = "isAutoMode";
   
   public static final String PROPERTY_IS_NOT_AUTOMODE = "isNotAutoMode";
   
   public static final String PROPERTY_PROOF_NOT_CLOSED = "proofIsNotClosed";
   
   
   
   @Override
   public boolean test(Object receiver, String property, Object[] args,
         Object expectedValue) {
      if (WorkbenchUtil.findView(ManualView.VIEW_ID) != null) {
         ManualView view = (ManualView) WorkbenchUtil.findView(ManualView.VIEW_ID);
         if (view.getProof() != null) {
            if (view.getProof().isDisposed()) {
               return false;
            }
         }
         if (view.getEnvironment() != null) {
            ProofControl proofControl = view.getEnvironment().getProofControl();
            if (proofControl != null) {
               if (property.equals(PROPERTY_IS_AUTO_MODE)) {
                  return proofControl.isInAutoMode();
               }
               if (property.equals(PROPERTY_IS_NOT_AUTOMODE)) {
                  return !proofControl.isInAutoMode();
               }
               if (property.equals(PROPERTY_PROOF_NOT_CLOSED)) {
                  return !view.getProof().closed();
               }
            }
         }
      }
      return false;
   }
   
   

}
