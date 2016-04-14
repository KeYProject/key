package org.key_project.sed.key.ui.propertyTester;

import org.eclipse.core.expressions.PropertyTester;
import org.eclipse.ui.IViewPart;
import org.key_project.sed.key.ui.view.ProofView;
import org.key_project.util.eclipse.WorkbenchUtil;

import de.uka.ilkd.key.control.ProofControl;

/**
 * tests the properties that are needed for starting and stopping auto mode on {@link ProofView}.
 * @author Seena Vellaramkalayil
 *
 */
public class AutoModePropertyTesterSED extends PropertyTester {

   /**
    * the namespace of the property tester.
    */
   public static final String PROPERTY_NAMESPACE = "org.key_project.sed.key.ui";
   
   /**
    * property "isAutoMode".
    */
   public static final String PROPERTY_IS_AUTO_MODE = "isAutoMode";
   
   /**
    * property "isNotAutoMde".
    */
   public static final String PROPERTY_IS_NOT_AUTOMODE = "isNotAutoMode";
   
   /**
    * property "proofIsNotClosed".
    */
   public static final String PROPERTY_PROOF_NOT_CLOSED = "proofIsNotClosed";
   
   
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean test(Object receiver, String property, Object[] args,
         Object expectedValue) {
         IViewPart tempView = WorkbenchUtil.findView(ProofView.VIEW_ID);
         if (tempView != null) {
            if (tempView instanceof ProofView) {
               ProofView view = (ProofView) tempView;
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
         }
      return false;
   }
   
   

}
