package org.key_project.sed.key.ui.propertyTester;

import org.eclipse.core.expressions.PropertyTester;
import org.key_project.sed.key.core.model.KeYDebugTarget;
import org.key_project.sed.key.ui.view.ProofView;
import org.key_project.util.eclipse.WorkbenchUtil;

/**
 * Tests properties of the {@link ProofView}.
 * @author Martin Hentschel
 */
public class ProofViewPropertyTester extends PropertyTester {
   /**
    * Property that the {@link ProofView} is opened and has a {@link KeYDebugTarget}.
    */
   public static final String PROOF_VIEW_HAS_DEBUG_TARGET = "proofViewHasDebugTarget";
   
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean test(Object receiver, String property, Object[] args, Object expectedValue) {
      if (PROOF_VIEW_HAS_DEBUG_TARGET.equals(property)) {
         ProofView view = (ProofView) WorkbenchUtil.findView(ProofView.VIEW_ID);
         return view != null && view.getKeyDebugTarget() != null;
      }
      else {
         return false;
      }
   }
}
