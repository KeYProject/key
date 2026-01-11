/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.conditions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.rule.VariableConditionAdapter;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

import de.uka.ilkd.key.java.declaration.*;
import de.uka.ilkd.key.java.expression.operator.TypeOperator;

import org.key_project.logic.SyntaxElement;
import org.key_project.logic.op.sv.SchemaVariable;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.ldt.HeapLDT;
import org.key_project.logic.op.Function;

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

        if (var != variable) return true;

        var inst = svInst.getInstantiation(variable);

        if (inst instanceof TypeOperator) {
            var out = ((TypeOperator)inst)
                .getAnnotations()
                .stream()
                .anyMatch(a -> a.getTypeReferenceAt(0).getName().equals(annot));
            return out;
        } else if (!(inst instanceof JTerm)) return false;
        var op = ((JTerm) inst).op();

        if (op.arity() != 0) return false;

        if (op instanceof Function) {
            return matchesField(services, (Function)op);
        }

        return false;
    }

    public boolean matchesField(Services services, Function op) {
        var kpmi = services.getJavaInfo().getKeYProgModelInfo();

        HeapLDT.SplitFieldName name = HeapLDT.trySplitFieldName(op);
        if (name == null) return false;

        var classType = ((Services) services).getJavaInfo()
            .getTypeByName(name.className());

        if (classType == null || 
                !(classType.getJavaType() instanceof ClassDeclaration)) return false;
        
        var recoderTypeDecl = (recoder.java.declaration.TypeDeclaration)
            kpmi.rec2key().toRecoder(classType);

        var fields = recoderTypeDecl.getAllFields();
        var field = fields.stream()
            .filter(f -> f.getName().equals(name.attributeName()))
            .findFirst()
            .orElse(null);

        if (field == null) return false;

        var fType = field.getContainingClassType();
        if (!(fType instanceof recoder.java.declaration.TypeDeclaration)) return false;

        var fieldSpec = ((recoder.java.declaration.TypeDeclaration)fType)
            .getFields().stream()
            .filter(spec -> spec.getName().equals(name.attributeName()))
            .findFirst()
            .orElse(null);

        if (fieldSpec == null) return false;

        var fieldDecl = fieldSpec.getParent();
        var declAnnotations = fieldDecl.getAnnotations();
        var value = declAnnotations.stream()
            .anyMatch(a -> a.getTypeReference().getName().equals(annot));

        return value;
    }

    @Override
    public String toString() {
        return "\\hasAnnotation(" + variable + ", " + annot + ")";
    }
}
