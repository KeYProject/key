package org.key_project.util.eclipse.swt;

import org.eclipse.swt.events.VerifyEvent;
import org.eclipse.swt.events.VerifyListener;
import org.key_project.util.java.StringUtil;

/**
 * This {@link VerifyListener} can be used to ensure that valid integers are defined.
 * @author Martin Hentschel
 */
public class IntegerVerifyListener implements VerifyListener {
   /**
    * The allowed minimal value.
    */
   private final int minValue;
   
   /**
    * The allowed maximal value.
    */
   private final int maxValue;
   
   /**
    * Allow empty strings?
    */
   private final boolean allowEmpty;

   /**
    * Constructor.
    * @param minValue The allowed minimal value.
    * @param maxValue The allowed maximal value.
    * @param allowEmpty Allow empty strings?
    */
   public IntegerVerifyListener(int minValue, int maxValue, boolean allowEmpty) {
      this.minValue = minValue;
      this.maxValue = maxValue;
      this.allowEmpty = allowEmpty;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void verifyText(VerifyEvent e) {
      try {
         String newText = SWTUtil.getNewText(e);
         if (StringUtil.isEmpty(newText)) {
            e.doit = allowEmpty;
         }
         else {
            int value = Integer.parseInt(newText);
            if (value < minValue) {
               e.doit = false;
            }
            else if (value > maxValue) {
               e.doit = false;
            }
         }
      }
      catch (Exception exc) {
         e.doit = false;
      }
   }
}
