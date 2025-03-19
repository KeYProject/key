/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.service;

import java.util.List;

import recoder.abstraction.*;
import recoder.abstraction.Package;
import recoder.java.reference.*;

/**
 * Source information service supporting cross reference information.
 *
 * @author AL
 */
public interface CrossReferenceSourceInfo extends SourceInfo {

    /**
     * Returns the list of references to a given method (or constructor). The references stem from
     * all known compilation units.
     *
     * @param m a method.
     * @return the possibly empty list of references to the given method.
     */
    List<MemberReference> getReferences(Method m);

    /**
     * Returns the list of references to a given constructor. The references stem from all known
     * compilation units.
     *
     * @param m a constructor.
     * @return the possibly empty list of references to the given constructor.
     */
    List<ConstructorReference> getReferences(Constructor m);

    /**
     * Returns the list of references to a given variable. The references stem from all known
     * compilation units.
     *
     * @param v a variable.
     * @return the possibly empty list of references to the given variable.
     */
    List<VariableReference> getReferences(Variable v);

    /**
     * Returns the list of references to a given field. The references stem from all known
     * compilation units.
     *
     * @param f a field.
     * @return the possibly empty list of references to the given field.
     */
    List<FieldReference> getReferences(Field f);

    /**
     * Returns the list of references to a given type. The references stem from all known
     * compilation units.
     *
     * @param t a type.
     * @return the possibly empty list of references to the given type.
     */
    List<TypeReference> getReferences(Type t);

    /**
     * Returns the list of references to a given package. The references stem from all known
     * compilation units.
     *
     * @param p a package.
     * @return the possibly empty list of references to the given package.
     */
    List<PackageReference> getReferences(Package p);

}
