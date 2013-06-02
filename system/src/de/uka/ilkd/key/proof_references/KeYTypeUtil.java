// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.proof_references;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;

/**
 * Provides utility methods which makes it easier to analyze the type hierarchy
 * of {@link KeYJavaType} instances with help of given {@link Services}.
 * @author Martin Hentschel
 */
public final class KeYTypeUtil {
   /**
    * Separator between packages and types.
    */
   public static final String PACKAGE_SEPARATOR = ".";

   /**
    * Forbid instances.
    */
   private KeYTypeUtil() {
   }

   /**
    * Checks if the given type is an inner or anonymous type.
    * @param services The {@link Services} to use.
    * @param type The type to check.
    * @return {@code true} is inner or anonymous, {@code false} is not
    */
   public static boolean isInnerType(Services services, KeYJavaType type) {
      String parentName = getParentName(services, type);
      if (parentName != null) {
         return !services.getJavaInfo().isPackage(parentName);
      }
      else {
         return false; // Normal class in default package
      }
   }
   
   /**
    * Returns the name of the parent package/type or {@code null} if it has no one.
    * @param services The {@link Services} to use.
    * @param type The type.
    * @return The parent package/type or {@code null} if it has no one.
    */
   public static String getParentName(Services services, KeYJavaType type) {
      return type != null ? getParentName(services, type.getFullName()) : null;
   }
   
   /**
    * Returns the name of the parent package/type or {@code null} if it has no one.
    * @param services The {@link Services} to use.
    * @param fullName The name of the current package/type.
    * @return The parent package/type or {@code null} if it has no one.
    */
   private static String getParentName(Services services, String fullName) {
      int lastSeparator = fullName.lastIndexOf(PACKAGE_SEPARATOR);
      if (lastSeparator >= 0) {
         String parentName = fullName.substring(0, lastSeparator);
         // Check if parentName is existing package or type (required for anonymous classes that have multiple numbers like ClassContainer.DefaultChildClass.23543334.10115480)
         if (services.getJavaInfo().isPackage(parentName)) {
            return parentName;
         }
         else if (isType(services, parentName)) {
            return parentName;
         }
         else {
            return getParentName(services, parentName);
         }
      }
      else {
         return null;
      }
   }
   
   /**
    * Checks if the given full name is a type in KeY.
    * @param services The services to use.
    * @param fullName The full name to check.
    * @return {@code true} = is type, {@code false} = is no type
    */
   public static boolean isType(Services services, String fullName) {
      return getType(services, fullName) != null;
   }
   
   /**
    * Returns the {@link KeYJavaType} fore the given name.
    * @param services The {@link Services} to use.
    * @param fullName The full name of the requested {@link KeYJavaType}.
    * @return The found {@link KeYJavaType} or {@code null} if no type exist with the given name.
    */
   public static KeYJavaType getType(Services services, String fullName) {
      try {
         return services.getJavaInfo().getKeYJavaType(fullName); 
      }
      catch (Exception e) {
         return null; // RuntimeException is thrown if type not exist.
      }
   }
}