/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.conditions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.Annotation;
import de.uka.ilkd.key.java.ast.annotation.MarkerAnnotation;
import de.uka.ilkd.key.java.ast.expression.operator.New;
import de.uka.ilkd.key.java.ast.reference.TypeRef;
import de.uka.ilkd.key.java.ast.reference.TypeReference;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

import org.key_project.prover.rules.VariableCondition;
import org.key_project.prover.rules.instantiation.MatchResultInfo;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.logic.LogicServices;
import org.key_project.logic.SyntaxElement;
import org.key_project.logic.op.sv.SchemaVariable;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.util.Arrays;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

public final class AddAnnotation implements VariableCondition {
    private static final Logger LOGGER = LoggerFactory.getLogger(AddAnnotation.class);

    private final SchemaVariable read, store;
    private final String annot;


    public AddAnnotation(SchemaVariable store, SchemaVariable read, String annot) {
        assert store.sort().toString().equals("SimpleInstanceCreation") 
            && read.sort().toString().equals("SimpleInstanceCreation");

        this.read = read;
        this.store = store;
        this.annot = annot;
    }

    @Override
    public MatchResultInfo check(@Nullable SchemaVariable var, @Nullable SyntaxElement instCandidate,
            @NonNull MatchResultInfo matchCond, @NonNull LogicServices logicServices) {

        final var svInst = (SVInstantiations) matchCond.getInstantiations();

        if (svInst.getInstantiation(store) != null || 
                svInst.getInstantiation(read) == null) {
            return matchCond;
        }

        Object inst = svInst.getInstantiation(read);

        if (!(inst instanceof New))
            return matchCond;

        var annotation = build((Services)logicServices);
        var replacement = addAnnotToNew((New)inst, annotation);

        return matchCond.setInstantiations(
                svInst.add(store, replacement, logicServices));
    }

    private Annotation build(Services services) {
        return new MarkerAnnotation(services.getJavaInfo().getTypeByName(annot));
    }

    private New addAnnotToNew(New n, Annotation annotation) {
        TypeReference nTypeRef = n.getTypeReference();
        var arr = new Annotation[nTypeRef.getAnnotations().size() + 1];
        n.getTypeReference().getAnnotations().arraycopy(0, arr, 1, arr.length - 1);
        arr[0] = annotation;
        var newAnnots = new ImmutableArray<>(arr);

        var newTypeRef = new TypeRef(
                nTypeRef.getProgramElementName(),
                newAnnots, nTypeRef.getDimensions(),
                nTypeRef.getReferencePrefix(),
                nTypeRef.getKeYJavaType());

        return new New(
                n.getPositionInfo(),
                Arrays.asList(n.getComments()),
                n.getArguments(),
                newTypeRef,
                n.getClassDeclaration());
    }

    @Override
    public String toString() {
        return "\\addAnnotation(" + store + ", " + read + ", " + annot + ")";
    }
}
