package org.key_project.ncore.java;

import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.TypeDeclaration;

public class PreSteps {
    interface PreStep {
        void applyOn(NodeList<TypeDeclaration<?>> types);
    }
}
