/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.ast;

import java.util.*;

import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;

import com.github.javaparser.resolution.MethodUsage;
import com.github.javaparser.resolution.declarations.*;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.resolution.types.ResolvedType;
import org.jspecify.annotations.NonNull;

/**
 * @author Alexander Weigl
 * @version 1 (23.06.23)
 */
public class ResolvedLogicalType implements ResolvedReferenceTypeDeclaration {
    @NonNull
    private final KeYJavaType keYJavaType;

    public ResolvedLogicalType(@NonNull KeYJavaType kjt) {
        this.keYJavaType = kjt;
    }

    @Override
    public List<ResolvedReferenceType> getAncestors(boolean acceptIncompleteList) {
        return Collections.emptyList();
    }

    @Override
    public List<ResolvedFieldDeclaration> getAllFields() {
        return Collections.emptyList();
    }

    @Override
    public Set<ResolvedMethodDeclaration> getDeclaredMethods() {
        return Collections.emptySet();
    }

    @Override
    public Set<MethodUsage> getAllMethods() {
        return Collections.emptySet();
    }

    @Override
    public boolean isAssignableBy(ResolvedType type) {
        return false;
    }

    @Override
    public boolean isAssignableBy(ResolvedReferenceTypeDeclaration other) {
        return false;
    }

    @Override
    public boolean hasDirectlyAnnotation(String qualifiedName) {
        return false;
    }

    @Override
    public boolean isFunctionalInterface() {
        return false;
    }

    @Override
    public List<ResolvedConstructorDeclaration> getConstructors() {
        return Collections.emptyList();
    }

    @Override
    public Optional<ResolvedReferenceTypeDeclaration> containerType() {
        return Optional.empty();
    }

    @Override
    public String getPackageName() {
        return "";
    }

    @Override
    public String getClassName() {
        return keYJavaType.getName();
    }

    @Override
    public String getQualifiedName() {
        return keYJavaType.getFullName();
    }

    @Override
    public String getName() {
        return keYJavaType.getName();
    }

    @Override
    public List<ResolvedTypeParameterDeclaration> getTypeParameters() {
        return Collections.emptyList();
    }

    @NonNull
    public KeYJavaType getKeYJavaType() {
        return keYJavaType;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o)
            return true;
        if (o == null || getClass() != o.getClass())
            return false;
        ResolvedLogicalType that = (ResolvedLogicalType) o;
        return Objects.equals(keYJavaType, that.keYJavaType);
    }

    @Override
    public int hashCode() {
        return Objects.hash(keYJavaType);
    }
}
