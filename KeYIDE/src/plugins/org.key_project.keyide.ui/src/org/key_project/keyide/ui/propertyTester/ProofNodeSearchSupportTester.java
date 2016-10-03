package org.key_project.keyide.ui.propertyTester;

import org.eclipse.core.expressions.PropertyTester;
import org.eclipse.ui.IWorkbenchPart;
import org.key_project.keyide.ui.util.IProofNodeSearchSupport;

/**
 * Tests to check if an {@link IProofNodeSearchSupport} is available.
 * @author Martin Hentschel
 */
public class ProofNodeSearchSupportTester extends PropertyTester {
   /**
    * The name of the start property.
    */
   public static final String PROPERTY_SUPPORTS_PROOF_NODE_SEARCH = "supportsProofNodeSearch";
   
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean test(Object receiver, String property, Object[] args, Object expectedValue) {
      if (PROPERTY_SUPPORTS_PROOF_NODE_SEARCH.equals(property)) {
         if (receiver instanceof IWorkbenchPart) {
            IWorkbenchPart part = (IWorkbenchPart) receiver;
            IProofNodeSearchSupport support = (IProofNodeSearchSupport) part.getAdapter(IProofNodeSearchSupport.class);
            return support != null;
         }
         else {
            return false;
         }
      }
      else {
         return true;
      }
   }
}
