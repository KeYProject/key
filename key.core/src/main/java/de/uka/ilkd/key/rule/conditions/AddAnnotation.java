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
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.logic.sort.ProgramSVSort;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

import org.key_project.prover.rules.VariableCondition;
import org.key_project.prover.rules.instantiation.MatchResultInfo;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.logic.LogicServices;
import org.key_project.logic.SyntaxElement;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.logic.sort.Sort;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.util.Arrays;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

public final class AddAnnotation implements VariableCondition {
    private static final Logger LOGGER = LoggerFactory.getLogger(AddAnnotation.class);
    private static final Sort[] ALLOWED = { ProgramSVSort.SIMPLE_NEW };

    private final SchemaVariable read, store;
    private final String annot;


    public AddAnnotation(SchemaVariable store, SchemaVariable read, String annot) {
        if (!store.sort().equals(read.sort())) {
            throw new RuntimeException("Expected left and right to have the same sort!");
        }

        if (!Arrays.stream(ALLOWED).anyMatch(read.sort()::equals)) {
            throw new RuntimeException(
                    "Unsupported sort: " + read.sort() + ", supported: " + 
                    Arrays.stream(ALLOWED).map(s -> s.toString()).reduce("", (a, b) -> a + " " + b));
        }

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

        Annotation annotation = build((Services)logicServices);
        TypeReference tRef = removeAnnotation(((New)inst).getTypeReference(), annotation);
        New replacement = newFromTypeRef((New)inst, tRef);

        return matchCond.setInstantiations(
                svInst.add(store, replacement, logicServices));
    }

    private Annotation build(Services services) {
        return new MarkerAnnotation(services.getJavaInfo().getTypeByName(annot));
    }

    private TypeReference removeAnnotation(TypeReference tRef, Annotation annotation) {
        var arr = new Annotation[tRef.getAnnotations().size() + 1];
        tRef.getAnnotations().arraycopy(0, arr, 1, arr.length - 1);
        arr[0] = annotation;
        var newAnnots = new ImmutableArray<>(arr);

        return new TypeRef(
                tRef.getProgramElementName(),
                newAnnots, tRef.getDimensions(),
                tRef.getReferencePrefix(),
                tRef.getKeYJavaType());
    }

    private static New newFromTypeRef(New n, TypeReference tRef) {
        return new New(
                n.getPositionInfo(),
                Arrays.asList(n.getComments()),
                n.getArguments(),
                tRef,
                n.getClassDeclaration());
    }

    @Override
    public String toString() {
        return "\\addAnnotation(" + store + ", " + read + ", " + annot + ")";
    }
}
