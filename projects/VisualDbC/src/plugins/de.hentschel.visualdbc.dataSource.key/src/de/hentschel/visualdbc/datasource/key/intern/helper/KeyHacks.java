/*******************************************************************************
 * Copyright (c) 2013 Karlsruhe Institute of Technology, Germany 
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

package de.hentschel.visualdbc.datasource.key.intern.helper;

import java.util.Map;

import org.eclipse.core.runtime.Assert;
import org.key_project.util.java.ObjectUtil;
import org.key_project.util.java.StringUtil;

import de.hentschel.visualdbc.datasource.model.exception.DSException;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.speclang.ClassInvariant;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.DependencyContract;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;
import de.uka.ilkd.key.speclang.FunctionalOperationContractImpl;

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
    * @param contract The operation contract to read from.
    * @return The pre condition.
    * @throws DSException Occurred Exception
    */
   public static String getOperationContractPre(Services services,
                                                Contract contract) throws DSException {
      try {
         // This implementation uses the code copied from de.uka.ilkd.key.speclang.OperationContractImpl#getHTMLText(de.uka.ilkd.key.java.Services); without the transformation to HTML.
         // An alternative possible solution will be to convert the HTML text back to plain text.
         // This realization is implemented, because it is easier and more performant. 
         Assert.isNotNull(contract);
         if (contract instanceof FunctionalOperationContractImpl) {
            final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
            final LocationVariable baseHeap = heapLDT.getHeap();
            Map<LocationVariable,Term> originalPres = ObjectUtil.get(contract, "originalPres");
            String pres = "";
            for(LocationVariable h : heapLDT.getAllHeaps()) {
               if(originalPres.get(h) != null) {
                 pres = pres + (h == baseHeap ? "" : "["+h+"]")+" " +
                   LogicPrinter.quickPrintTerm(originalPres.get(h),services);
               }
            }
            return StringUtil.trim(pres); // Trim the text to remove line breaks in the end
         }
         else {
            Map<LocationVariable, Term> originalPres = ObjectUtil.get(contract, "originalPres");
            String pres = "";
            for(LocationVariable h : originalPres.keySet()) {
               Term originalPre = originalPres.get(h);
               if(originalPre != null) {
                    pres = pres + "["+h+"] "+LogicPrinter.quickPrintTerm(originalPre, services);
               }
            }
            return StringUtil.trim(pres); // Trim the text to remove line breaks in the end
         }
      }
      catch (Exception e) {
         throw new DSException("Can't read pre condition from contract: " + contract, e);
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
         final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
         final LocationVariable baseHeap = heapLDT.getHeap();
         Map<LocationVariable,Term> originalPosts = ObjectUtil.get(operationContract, "originalPosts");
         String posts = "";
         for(LocationVariable h : heapLDT.getAllHeaps()) {
            if(originalPosts.get(h) != null) {
              posts = posts + (h == baseHeap ? "" : "["+h+"]")+" " +
                LogicPrinter.quickPrintTerm(originalPosts.get(h),services);
            }
         }
         return StringUtil.trim(posts); // Trim the text to remove line breaks in the end
      }
      catch (Exception e) {
         throw new DSException("Can't read post condition from operation contract: " + operationContract, e);
      }
   }

   /**
    * Reads the dep condition from the dependency contract.
    * @param services The services to use.
    * @param dependencyContract The dependency contract to read from.
    * @return The post condition.
    * @throws DSException Occurred Exception
    */   
   public static String getDependencyContractDep(Services services, DependencyContract dependencyContract) throws DSException {
      try {
         // This implementation uses the code copied from de.uka.ilkd.key.speclang.OperationContractImpl#getHTMLText(de.uka.ilkd.key.java.Services); without the transformation to HTML.
         // An alternative possible solution will be to convert the HTML text back to plain text.
         // This realization is implemented, because it is easier and more performant. 
         Assert.isNotNull(dependencyContract);
         Map<ProgramVariable,Term> originalDeps = ObjectUtil.get(dependencyContract, "originalDeps");
         String deps = "";
         for(ProgramVariable h : originalDeps.keySet()) {
             if(h.name().toString().endsWith("AtPre") && dependencyContract.getTarget().getStateCount() == 1) {
                  continue;
             }
             Term originalDep = originalDeps.get(h);
             if(originalDep != null) {
                 deps = deps + "["+h+"] "+LogicPrinter.quickPrintTerm(originalDep, services);
             }
         }
         return StringUtil.trim(deps); // Trim the text to remove line breaks in the end
      }
      catch (Exception e) {
         throw new DSException("Can't read dep condition from axiom contract: " + dependencyContract, e);
      }
   }
   
   /**
    * Reads the modifies from the operation contract.
    * @param services The services to use.
    * @param contract The operation contract to read from.
    * @return The modifies.
    * @throws DSException Occurred Exception
    */
   public static String getOperationContractModifies(Services services,
                                                     FunctionalOperationContract contract) throws DSException {
      try {
         // This implementation uses the code copied from de.uka.ilkd.key.speclang.FunctionalOperationContractImpl#getHTMLText(de.uka.ilkd.key.java.Services); without the transformation to HTML.
         // An alternative possible solution will be to convert the HTML text back to plain text.
         // This realization is implemented, because it is easier and more performant. 
         Assert.isNotNull(contract);
         Map<LocationVariable,Term> originalMods = ObjectUtil.get(contract, "originalMods");
         final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
         final LocationVariable baseHeap = heapLDT.getHeap();
         String mods = "";
         for(LocationVariable h : heapLDT.getAllHeaps()) {
            if(originalMods.get(h) != null) {
               mods = mods + "mod[" + h + "]: " + LogicPrinter.quickPrintTerm(originalMods.get(h), services);
               if(h == baseHeap && !contract.hasModifiesClause(h)) {
                  mods = mods + ", creates no new objects";
               }
            }
         }
         return StringUtil.trim(mods); // Trim the text to remove line breaks in the end
      }
      catch (Exception e) {
         throw new DSException("Can't read post condition from operation contract: " + contract, e);
      }
   }
}