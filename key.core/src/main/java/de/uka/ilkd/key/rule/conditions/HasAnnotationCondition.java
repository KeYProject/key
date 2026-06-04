/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.conditions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.ProgramElement;
import de.uka.ilkd.key.java.ast.declaration.*;
import de.uka.ilkd.key.java.ast.reference.TypeReference;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.rule.VariableConditionAdapter;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

import org.key_project.logic.SyntaxElement;
import org.key_project.logic.op.Function;
import org.key_project.logic.op.sv.SchemaVariable;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public final class HasAnnotationCondition extends VariableConditionAdapter {
    private static final Logger LOGGER = LoggerFactory.getLogger(HasAnnotationCondition.class);

    private final SchemaVariable variable;
    private final String annot;

    public HasAnnotationCondition(SchemaVariable variable, String annot) {
        this.variable = variable;
        this.annot = annot;
    }

    @Override
    public boolean check(SchemaVariable var, SyntaxElement subst,
            SVInstantiations svInst, Services services) {

        if (var != variable)
            return true;

        Object inst = svInst.getInstantiation(variable);

        if (!(inst instanceof JTerm))
            return false;

        var op = ((JTerm) inst).op();

        if (op.arity() != 0)
            return false;

        if (op instanceof Function) {
            return matchesTypeAnnots(getFieldType(services, (Function) op));
        } else if (op instanceof ProgramVariable variable) {
            return matchesTypeAnnots(variable.getTypeReference());
        }

        return false;
    }

    public TypeReference getFieldType(Services services, Function op) {
        HeapLDT.SplitFieldName name = HeapLDT.trySplitFieldName(op);

        if (name == null) return null;

        var classType = ((Services) services).getJavaInfo()
                .getTypeByName(name.className());

        if (classType == null ||
                !(classType.getJavaType() instanceof ClassDeclaration))
            return null;

        var classDecl = (ClassDeclaration) classType.getJavaType();

        var fields = classDecl.getAllFields(services);

        // this is a bit too brittle for me
        var field = fields.stream()
                .filter(f -> f.getName().split("::")[1].equals(name.attributeName()))
                .findFirst()
                .orElse(null);

        if (field == null) return null;

        return field.getProgramVariable().getTypeReference();
    }

    private boolean matchesTypeAnnots(TypeReference typeRef) {
        if (typeRef == null) return false;
        return typeRef.getAnnotations().stream()
            .anyMatch(a -> a.getKeyJavaType().getFullName().equals(annot));
    }

    @Override
    public String toString() {
        return "\\hasAnnotation(" + variable + ", " + annot + ")";
    }
}
