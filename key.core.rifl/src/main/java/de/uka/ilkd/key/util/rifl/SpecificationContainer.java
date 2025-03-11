/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.util.rifl;

import java.util.Set;

import de.uka.ilkd.key.util.rifl.SpecificationEntity.Type;

import recoder.java.declaration.FieldDeclaration;
import recoder.java.declaration.MethodDeclaration;

/**
 * Container for parsed RIFL specifications. Each query returns the assigned security level (domain)
 * for an element represented as a String, or null if the element is not assigned a domain. RIFL
 * specifications are not validated in any way. Categories in RIFL are currently treated opaque.
 *
 * @author bruns
 *
 */
public interface SpecificationContainer {

    /**
     * Return the security level of the field, represented as a String. Convenience method for
     * Recoder AST element.
     */
    String field(FieldDeclaration fd, Type type);

    /**
     * Return the security level of the field, represented as a String.
     */
    String field(String inPackage, String inClass, String name, Type type);

    /**
     * Return the security level of the method parameter, represented as a String. Convenience
     * method for Recoder AST element.
     */
    String parameter(MethodDeclaration md, int index, Type type);

    /**
     * Return the security level of the method parameter, represented as a String.
     */
    String parameter(String inPackage, String inClass, String methodName,
            String[] paramTypes, int index, Type type);

    /**
     * Return the security level of the method return, represented as a String. Convenience method
     * for Recoder AST element.
     */
    String returnValue(MethodDeclaration md, Type type);

    /**
     * Return the security level of the method return, represented as a String.
     */
    String returnValue(String inPackage, String inClass, String methodName,
            String[] paramTypes, Type type);

    /**
     * Return the domains from which the given domain flows
     */
    Set<String> flows(String domain);
}
