/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.ncore.java;

import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.body.TypeDeclaration;
import com.github.javaparser.ast.nodeTypes.NodeWithSimpleName;
import com.google.common.collect.Multimap;
import com.google.common.collect.MultimapBuilder;

import java.util.ArrayList;
import java.util.TreeMap;

import static com.github.javaparser.ast.Modifier.DefaultKeyword.ABSTRACT;
import static org.key_project.ncore.java.NodeSteps.isRoot;

public class PreSteps {
    final static class PreComputation implements PreStep {
        Multimap<String, String> inheritanceMap =
                MultimapBuilder.treeKeys().treeSetValues().build();
        Multimap<String, String> permittedTypes =
                MultimapBuilder.treeKeys().treeSetValues().build();

        ClassOrInterfaceDeclaration root;

        @Override
        public void applyOn(NodeList<TypeDeclaration<?>> types) {
            TreeMap<String, ClassOrInterfaceDeclaration> fields = new TreeMap<>();
            this.root = (ClassOrInterfaceDeclaration) types.stream()
                    .filter(decl -> decl instanceof ClassOrInterfaceDeclaration clazz
                            && isRoot(clazz))
                    .findFirst().get();

            for (TypeDeclaration<?> decl : types) {
                if (decl instanceof ClassOrInterfaceDeclaration clazz) {
                    if (isRoot(clazz)) {
                        this.root = clazz;
                    }
                    fields.put(decl.getNameAsString(), clazz);

                    inheritanceMap.put(decl.getNameAsString(), this.root.getNameAsString());
                    var zuper =
                            clazz.getExtendedTypes().getOFirst().map(NodeWithSimpleName::getNameAsString);
                    zuper.ifPresent(s -> inheritanceMap.put(decl.getNameAsString(), s));
                }
            }

            // compute transitive closure of inheritance
            boolean changed = true;
            while (changed) {
                changed = false;
                for (var clazz : inheritanceMap.keySet()) {
                    final var strings = new ArrayList<>(inheritanceMap.get(clazz));
                    for (var zuper : strings) {
                        changed =
                                changed || inheritanceMap.putAll(clazz, inheritanceMap.get(zuper));
                    }
                }
            }

            // inherit fields into terminal AST nodes
            for (var decl : fields.sequencedValues()) {
                if (decl.hasModifier(ABSTRACT)) {
                    continue;
                }

                var newFields = new TreeMap<String, FieldDeclaration>();
                for (var c : inheritanceMap.get(decl.getNameAsString())) {
                    final var classOrInterfaceDeclaration = fields.get(c);
                    if (classOrInterfaceDeclaration != null) {
                        for (FieldDeclaration it : classOrInterfaceDeclaration.getFields()) {
                            var name = it.getVariable(0).getNameAsString();
                            newFields.computeIfAbsent(name, (k) -> {
                                final var clone = it.clone();
                                clone.addAnnotation(Override.class.getName());
                                clone.setRange(null);
                                return clone;
                            });
                        }
                    }
                }

                // only inherit field, if not already exists. allows overriding of fields
                // with more specific type
                newFields.forEach((name, field) -> {
                    var f = decl.getFieldByName(name);
                    if (f.isPresent()) {
                        f.get().getAnnotationByName("Override");
                    } else {
                        decl.addMember(field);
                    }
                });
            }

            fillPermittedTypes();
        }

        private void fillPermittedTypes() {
            for (var entry : inheritanceMap.entries()) {
                permittedTypes.put(entry.getValue(), entry.getKey());
            }
        }
    }

    interface PreStep {
        void applyOn(NodeList<TypeDeclaration<?>> types);
    }
}
