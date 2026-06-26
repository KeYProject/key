/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.conditions;

import java.util.Arrays;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.abstraction.Field;
import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.ast.declaration.*;
import de.uka.ilkd.key.java.ast.expression.operator.New;
import de.uka.ilkd.key.java.ast.reference.TypeReference;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.sort.ProgramSVSort;
import de.uka.ilkd.key.rule.VariableConditionAdapter;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

import org.key_project.logic.SyntaxElement;
import org.key_project.logic.op.Function;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.logic.sort.Sort;
import org.key_project.util.collection.ImmutableList;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * This variable condition can be used to check if the {@link TypeReference} of a
 * {@link SchemaVariable} contains a specific {@link Annotation}.
 *
 * @author Daniel Grévent
 */
public final class HasAnnotationCondition extends VariableConditionAdapter {
    private static final Logger LOGGER = LoggerFactory.getLogger(HasAnnotationCondition.class);

    private static final Sort[] ALLOWED = {
        ProgramSVSort.SIMPLE_NEW,
        ProgramSVSort.LOCALVARIABLE, ProgramSVSort.VARIABLE,
    };

    private final SchemaVariable variable;
    private final String annot;

    /**
     * create an instance of the variable condition.
     *
     * @param variable the variable whos {@link TypeReference} is to check for
     *        {@link Annotation}s.
     * @param annot the fully qualified name of the {@link Annotation} to check for
     *
     * @throws IllegalArgumentException if `variable` is not one of the {@link Sort}s
     *         in the `ALLOWED` array or the {@link Sort} has the name `Field`.
     */
    public HasAnnotationCondition(SchemaVariable variable, String annot) {
        if (!Arrays.stream(ALLOWED).anyMatch(variable.sort()::equals) &&
                !variable.sort().toString().equals("Field")) {
            throw new IllegalArgumentException(
                "Unsupported sort: " + variable.sort() + ", supported: " +
                    Arrays.stream(ALLOWED).map(s -> s.toString()).reduce("",
                        (a, b) -> a + " " + b));
        }

        this.variable = variable;
        this.annot = annot;
    }

    @Override
    public boolean check(SchemaVariable var, SyntaxElement subst,
            SVInstantiations svInst, Services services) {

        if (var != variable)
            return true;

        Object inst = svInst.getInstantiation(variable);

        if (inst instanceof New n) {
            return matchesTypeAnnots(n.getTypeReference());
        } else if (inst instanceof ProgramVariable variable) {
            return matchesTypeAnnots(variable.getTypeReference());
        } else if (inst instanceof JTerm term &&
                term.op().arity() == 0 &&
                term.op() instanceof Function func) {
            return matchesTypeAnnots(getFieldType(services, func));
        }

        return false;
    }

    private TypeReference getFieldType(Services services, Function op) {
        HeapLDT.SplitFieldName name = HeapLDT.trySplitFieldName(op);

        if (name == null)
            return null;

        KeYJavaType classType = services.getJavaInfo().getTypeByName(name.className());

        if (classType != null
                && classType.getJavaType() instanceof ClassDeclaration classDecl) {
            ImmutableList<Field> fields = classDecl.getAllFields(services);

            return fields.stream()
                    .filter(f -> f.getName().split("::")[1].equals(name.attributeName()))
                    .findFirst()
                    .map(f -> f.getProgramVariable().getTypeReference())
                    .orElse(null);
        }


        return null;
    }

    private boolean matchesTypeAnnots(TypeReference typeRef) {
        if (typeRef == null)
            return false;

        return typeRef.getAnnotations().stream()
                .anyMatch(a -> a.getKeyJavaType().getFullName().equals(annot));
    }

    @Override
    public String toString() {
        return "\\hasAnnotation(" + variable + ", " + annot + ")";
    }
}
