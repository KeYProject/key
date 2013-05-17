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

package org.key_project.key4eclipse.test.util;

import org.key_project.util.java.StringUtil;

/**
 * Provides static methods that makes testing easier.
 * @author Martin Hentschel
 */
public final class TestKeY4EclipseUtil {
   /**
    * Forbid instances.
    */
   private TestKeY4EclipseUtil() {
   }
   
   /**
    * Creates an operation contract ID.
    * @param qualifiedName The qualified class name.
    * @param methodClassQualifiedName The name of the class which contains the method implementation.
    * @param method The method signature.
    * @param id The unique ID.
    * @param behavior The behavior.
    * @return The created operation contract ID:
    */
   public static String createOperationContractId(String qualifiedName,
                                                  String methodClassQualifiedName,
                                                  String method,
                                                  String id,
                                                  String behavior) {
      return qualifiedName + "[" + methodClassQualifiedName + "::" + method + "].JML " + (StringUtil.isEmpty(behavior) ? "" : behavior + " ") + "operation contract." + id + "";
   }

   /**
    * Creates the ID for an axiom contract.
    * @param qualifiedName The full qualified class name.
    * @param field The field.
    * @param id The unique ID.
    * @return the create axiom contract ID.
    */
   public static String createAxiomContractId(String qualifiedName, String field, String id) {
      return createCompleteAxiomContractId(qualifiedName, qualifiedName + "::" + field, id);
   }

   /**
    * Creates the ID for an axiom contract.
    * @param qualifiedName The full qualified class name.
    * @param field The field.
    * @param id The unique ID.
    * @return the create axiom contract ID.
    */
   public static String createCompleteAxiomContractId(String qualifiedName, String field, String id) {
      return qualifiedName + "[" + field + "].JML accessible clause." + id;
   }
}