package org.key_project.sed.key.ui.propertyTester;

import org.eclipse.core.expressions.PropertyTester;
import org.eclipse.ui.IViewPart;
import org.key_project.keyide.ui.propertyTester.AutoModePropertyTester;
import org.key_project.keyide.ui.propertyTester.ProofPropertyTester;
import org.key_project.sed.key.ui.view.ProofView;
import org.key_project.util.eclipse.WorkbenchUtil;

/**
 * tests the properties that are needed for starting and stopping auto mode on {@link ProofView}.
 * @author Seena Vellaramkalayil
 */
public class AutoModePropertyTesterSED extends PropertyTester {
   /**
    * the namespace of the property tester.
    */
   public static final String PROPERTY_NAMESPACE = "org.key_project.sed.key.ui";
   
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean test(Object receiver, String property, Object[] args, Object expectedValue) {
      IViewPart view = WorkbenchUtil.findView(ProofView.VIEW_ID);
      if (view instanceof ProofView) {
         ProofView proofView = (ProofView) view;
         if (property.equals(ProofPropertyTester.PROPERTY_IS_NOT_CLOSED)) {
            return ProofPropertyTester.testProofProvider(proofView, property);
         }
         else {
            return AutoModePropertyTester.testProofProvider(proofView, property);
         }
      }
      else {
         return false;
      }
   }

   /**
    * Re-evaluates all properties defined by this {@link PropertyTester}.
    */
   public static void updateProperties() {
      WorkbenchUtil.updatePropertyTesters(PROPERTY_NAMESPACE + "." + AutoModePropertyTester.PROPERTY_IS_NOT_AUTO_MODE, 
                                          PROPERTY_NAMESPACE + "." + AutoModePropertyTester.PROPERTY_IS_AUTO_MODE, 
                                          PROPERTY_NAMESPACE + "." + ProofPropertyTester.PROPERTY_IS_NOT_CLOSED);
   }
}
