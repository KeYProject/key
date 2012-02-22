/*******************************************************************************
 * Copyright (c) 2011 Martin Hentschel.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Martin Hentschel - initial API and implementation
 *******************************************************************************/

package de.hentschel.visualdbc.datasource.key.intern.helper;

import org.eclipse.core.runtime.Assert;
import org.key_project.util.java.ObjectUtil;
import org.key_project.util.java.StringUtil;

import de.hentschel.visualdbc.datasource.model.exception.DSException;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.speclang.ClassInvariant;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;

/**
 * Provides static methods that uses java reflections to access not public
 * content or to do other illegal things.
 * @author Martin Hentschel
 */
public final class KeyHacks {
   /**
    * Forbid instances by this private constructor.
    */
   private KeyHacks() {
   }
   
   /**
    * Reads the text from the class invariant.
    * @param services The services to use.
    * @param classInvariant The class invariant to read the text from.
    * @return The class invariant text.
    * @throws DSException Occurred Exception
    */
   public static String getClassInvariantText(Services services,
                                              ClassInvariant classInvariant) throws DSException {
      try {
         // This implementation uses the code copied from de.uka.ilkd.key.speclang.ClassInvariantImpl#getHTMLText(de.uka.ilkd.key.java.Services); without the transformation to HTML.
         // An alternative possible solution will be to convert the HTML text back to plain text.
         // This realization is implemented, because it is easier and more performant. 
         Assert.isNotNull(classInvariant);
         Term originalInv = classInvariant.getOriginalInv();
         String inv = LogicPrinter.quickPrintTerm(originalInv, services);
         return StringUtil.trim(inv); // Trim the text to remove line breaks in the end
      }
      catch (Exception e) {
         throw new DSException("Can't read text from class invariant: " + classInvariant, e);
      }
   }
   
   /**
    * Reads the pre condition from the operation contract.
    * @param services The services to use.
    * @param operationContract The operation contract to read from.
    * @return The pre condition.
    * @throws DSException Occurred Exception
    */
   public static String getOperationContractPre(Services services,
                                                FunctionalOperationContract operationContract) throws DSException {
      try {
         // This implementation uses the code copied from de.uka.ilkd.key.speclang.OperationContractImpl#getHTMLText(de.uka.ilkd.key.java.Services); without the transformation to HTML.
         // An alternative possible solution will be to convert the HTML text back to plain text.
         // This realization is implemented, because it is easier and more performant. 
         Assert.isNotNull(operationContract);
         Term originalPre = ObjectUtil.get(operationContract, "originalPre");
         String inv = LogicPrinter.quickPrintTerm(originalPre, services);
         return StringUtil.trim(inv); // Trim the text to remove line breaks in the end
      }
      catch (Exception e) {
         throw new DSException("Can't read pre condition from operation contract: " + operationContract, e);
      }
   }
   
   /**
    * Reads the post condition from the operation contract.
    * @param services The services to use.
    * @param operationContract The operation contract to read from.
    * @return The post condition.
    * @throws DSException Occurred Exception
    */
   public static String getOperationContractPost(Services services,
                                                 FunctionalOperationContract operationContract) throws DSException {
      try {
         // This implementation uses the code copied from de.uka.ilkd.key.speclang.OperationContractImpl#getHTMLText(de.uka.ilkd.key.java.Services); without the transformation to HTML.
         // An alternative possible solution will be to convert the HTML text back to plain text.
         // This realization is implemented, because it is easier and more performant. 
         Assert.isNotNull(operationContract);
         Term originalPost = ObjectUtil.get(operationContract, "originalPost");
         String inv = LogicPrinter.quickPrintTerm(originalPost, services);
         return StringUtil.trim(inv); // Trim the text to remove line breaks in the end
      }
      catch (Exception e) {
         throw new DSException("Can't read post condition from operation contract: " + operationContract, e);
      }
   }
   
   /**
    * Reads the modifies from the operation contract.
    * @param services The services to use.
    * @param operationContract The operation contract to read from.
    * @return The modifies.
    * @throws DSException Occurred Exception
    */
   public static String getOperationContractModifies(Services services,
                                                     FunctionalOperationContract operationContract) throws DSException {
      try {
         // This implementation uses the code copied from de.uka.ilkd.key.speclang.OperationContractImpl#getHTMLText(de.uka.ilkd.key.java.Services); without the transformation to HTML.
         // An alternative possible solution will be to convert the HTML text back to plain text.
         // This realization is implemented, because it is easier and more performant. 
         Assert.isNotNull(operationContract);
         Term originalModifies = ObjectUtil.get(operationContract, "originalMod");
         String inv = LogicPrinter.quickPrintTerm(originalModifies, services);
         return StringUtil.trim(inv); // Trim the text to remove line breaks in the end
      }
      catch (Exception e) {
         throw new DSException("Can't read post condition from operation contract: " + operationContract, e);
      }
   }
}
