// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.proof_references;

import java.util.Iterator;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.ParameterDeclaration;
import de.uka.ilkd.key.java.declaration.TypeDeclaration;
import de.uka.ilkd.key.java.recoderext.ConstructorNormalformBuilder;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.symbolic_execution.util.IFilter;
import de.uka.ilkd.key.symbolic_execution.util.JavaUtil;

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

   /**
    * Checks if the given {@link KeYJavaType} is a library class.
    * @param kjt The {@link KeYJavaType} to check.
    * @return {@code true} is library class, {@code false} is no library class.
    */
   public static boolean isLibraryClass(KeYJavaType kjt) {
      return kjt != null && 
             kjt.getJavaType() instanceof TypeDeclaration && 
             ((TypeDeclaration)kjt.getJavaType()).isLibraryClass();
   }
   
   /**
    * Checks if the given {@link IProgramMethod} is an implicit constructor.
    * @param pm The {@link IProgramMethod} to check.
    * @return {@code true} is implicit constructor, {@code false} is no implicit constructor (e.g. method or explicit construcotr).
    */
   public static boolean isImplicitConstructor(IProgramMethod pm) {
      return pm != null && ConstructorNormalformBuilder.CONSTRUCTOR_NORMALFORM_IDENTIFIER.equals(pm.getName());
   }

   /**
    * Returns the {@link IProgramMethod} of the explicit constructor for
    * the given implicit constructor.
    * @param services The {@link Services} to use.
    * @param implicitConstructor The implicit constructor.
    * @return The found explicit constructor or {@code null} if not available.
    */
   public static IProgramMethod findExplicitConstructor(Services services, final IProgramMethod implicitConstructor) {
      if (services != null && implicitConstructor != null) {
         ImmutableList<IProgramMethod> pms = services.getJavaInfo().getConstructors(implicitConstructor.getContainerType());
         return JavaUtil.search(pms, new IFilter<IProgramMethod>() {
            @Override
            public boolean select(IProgramMethod element) {
               if (implicitConstructor.getParameterDeclarationCount() == element.getParameterDeclarationCount()) {
                  Iterator<ParameterDeclaration> implicitIter = implicitConstructor.getParameters().iterator();
                  Iterator<ParameterDeclaration> elementIter = element.getParameters().iterator();
                  boolean sameTypes = true;
                  while (sameTypes && implicitIter.hasNext() && elementIter.hasNext()) {
                     ParameterDeclaration implicitNext = implicitIter.next();
                     ParameterDeclaration elementNext = elementIter.next();
                     sameTypes = implicitNext.getTypeReference().equals(elementNext.getTypeReference());
                  }
                  return sameTypes;
               }
               else {
                  return false;
               }
            }
         });
      }
      else {
         return null;
      }
   }
}