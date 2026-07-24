/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.conditions;

import java.util.Arrays;

import de.uka.ilkd.key.java.ast.Annotation;
import de.uka.ilkd.key.java.ast.expression.operator.New;
import de.uka.ilkd.key.java.ast.reference.TypeRef;
import de.uka.ilkd.key.java.ast.reference.TypeReference;
import de.uka.ilkd.key.logic.sort.ProgramSVSort;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

import org.key_project.logic.LogicServices;
import org.key_project.logic.SyntaxElement;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.logic.sort.Sort;
import org.key_project.prover.rules.VariableCondition;
import org.key_project.prover.rules.instantiation.MatchResultInfo;
import org.key_project.util.collection.ImmutableArray;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;


/**
 * This variable condition can be used to create a copy of a {@link SchemaVariable}
 * that has all instances of an {@link Annotation} removed from its
 * {@link TypeReference}.
 *
 * @author Daniel Grévent
 */
public final class RemoveAnnotation implements VariableCondition {
    private static final Logger LOGGER = LoggerFactory.getLogger(RemoveAnnotation.class);

    private static final Sort[] ALLOWED = { ProgramSVSort.SIMPLE_NEW };

    private final SchemaVariable read, store;
    private final String annot;

    /**
     * create an instance of the variable condition.
     *
     * @param store the {@link SchemaVariable} in which the new copy is stored
     * @param read the {@link SchemaVariable} that gets copied
     * @param annot the fully qualified name of the {@link Annotation} to remove
     *
     * @throws IllegalArgumentException if `read` is not one of the {@link Sort}s in the
     *         `ALLOWED` array or the {@link Sort} of write is not the same as to {@link Sort}
     *         of `read`, so they do not correspond to the same kind of AST type.
     */
    public RemoveAnnotation(SchemaVariable store, SchemaVariable read, String annot) {
        if (!store.sort().equals(read.sort())) {
            throw new RuntimeException("Expected left and right to have the same sort!");
        }

        if (!Arrays.stream(ALLOWED).anyMatch(read.sort()::equals)) {
            throw new RuntimeException(
                "Unsupported sort: " + read.sort() + ", supported: " +
                    Arrays.stream(ALLOWED).map(s -> s.toString()).reduce("",
                        (a, b) -> a + " " + b));
        }

        this.read = read;
        this.store = store;
        this.annot = annot;
    }

    @Override
    public MatchResultInfo check(@Nullable SchemaVariable var,
            @Nullable SyntaxElement instCandidate,
            @NonNull MatchResultInfo matchCond, @NonNull LogicServices logicServices) {

        final var svInst = (SVInstantiations) matchCond.getInstantiations();

        if (svInst.getInstantiation(store) != null ||
                svInst.getInstantiation(read) == null) {
            return matchCond;
        }

        if (svInst.getInstantiation(read) instanceof New n) {
            TypeReference tRef = removeAnnotation(n.getTypeReference());
            New replacement = newFromTypeRef(n, tRef);

            return matchCond.setInstantiations(
                svInst.add(store, replacement, logicServices));
        }

        return matchCond;
    }

    private TypeReference removeAnnotation(TypeReference tRef) {
        Annotation[] filtered = tRef.getAnnotations()
                .stream()
                .filter(a -> !a.getKeyJavaType().getFullName().equals(annot))
                .toArray(Annotation[]::new);

        return new TypeRef(
            tRef.getProgramElementName(),
            new ImmutableArray<>(filtered), tRef.getDimensions(),
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
