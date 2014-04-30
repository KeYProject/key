/*******************************************************************************
 * Copyright (c) 2014 Karlsruhe Institute of Technology, Germany
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

package de.hentschel.visualdbc.datasource.model;

/**
 * Defines possible solutions to handle packages.
 * @author Martin Hentschel
 */
public enum DSPackageManagement {
   /**
    * <p>
    * Ignore packages and use fullqualified names in types.
    * </p>
    * <p>
    * Example:
    * <ul>
    * <li>Type: classA</li>
    * <li>Type: packageA.interfaceA</li>
    * <li>Type: packageA.packabeB.classB</li>
    * </ul>
    * </p>
    */
   NO_PACKAGES("No packages"),
   
   /**
    * <p>
    * Only flat package list without hierarchy and fullqualified package names.
    * Types have only the type simple name.
    * </p>
    * <p>
    * Example:
    * <ul>
    * <li>Type: classA</li>
    * <li>
    *    Package: packageA
    *    <ul>
    *       <li>Type: interfaceA</li>
    *    </ul>
    * </li>
    * <li>
    *    Package: packageA.packabeB
    *    <ul>
    *       <li>Type: classB</li>
    *    </ul>
    * </li>
    * </ul>
    * </p>
    */
   FLAT_LIST("Flat list"),
   
   /**
    * <p>
    * Hierarchy of packages. Package and type names are only the simple name.
    * </p>
    * <p>
    * Example:
    * <ul>
    * <li>Type: classA</li>
    * <li>
    *    Package: packageA
    *    <ul>
    *       <li>Type: interfaceA</li>
    *    </ul>
    * </li>
    * <li>
    *    Package: packageA
    *    <ul>
    *       <li>
    *          Package: packabeB
    *          <ul>
    *             <li>Type: classB</li>
    *          </ul>
    *       </li>
    *    </ul>
    * </li>
    * </ul>
    * </p>

    */
   HIERARCHY("Hierarchy");
   
   /**
    * The display text to use in the UI.
    */
   private String displayText;
   
   /**
    * Constructor.
    * @param displayText The display text to use in the UI.
    */
   private DSPackageManagement(String displayText) {
      this.displayText = displayText;
   }

   /**
    * Returns the display text to use in the UI.
    * @return The display text to use in the UI.
    */
   public String getDisplayText() {
      return displayText;
   }

   /**
    * Returns the default {@link DSPackageManagement}.
    * @return The default {@link DSPackageManagement}.
    */
   public static DSPackageManagement getDefault() {
      return FLAT_LIST;
   }
}