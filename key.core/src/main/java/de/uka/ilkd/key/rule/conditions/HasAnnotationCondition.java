/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.conditions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.ProgramElement;
import de.uka.ilkd.key.java.ast.declaration.*;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.op.LocationVariable;
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
            LOGGER.info("field {}", op);
            return matchesField(services, (Function) op);
        } else if (op instanceof ProgramElement) {
            if (op instanceof LocationVariable) {
                //LOGGER.info("type ref {}", ((LocationVariable)op).getTypeReference());
                //LOGGER.info("annotations {}", ((LocationVariable)op).getTypeReference().getAnnotations());
            }
        }

        return false;
    }

    public boolean matchesField(Services services, Function op) {
        HeapLDT.SplitFieldName name = HeapLDT.trySplitFieldName(op);

        if (name == null)
            return false;

        var classType = ((Services) services).getJavaInfo()
                .getTypeByName(name.className());

        if (classType == null ||
                !(classType.getJavaType() instanceof ClassDeclaration))
            return false;

        var classDecl = (ClassDeclaration)classType.getJavaType();

        var fields = classDecl.getAllFields(services);

        // this is a bit too brittle for me
        var field = fields.stream()
            .filter(f -> f.getName().split("::")[1].equals(name.attributeName()))
            .findFirst()
            .orElse(null);
        
        if (field == null) return false;
        
        var fieldType = field.getProgramVariable().getTypeReference();
        var declAnnotations = fieldType.getAnnotations();
        return declAnnotations.stream().anyMatch(a -> a.getName().equals(annot));
    }

    @Override
    public String toString() {
        return "\\hasAnnotation(" + variable + ", " + annot + ")";
    }
}
