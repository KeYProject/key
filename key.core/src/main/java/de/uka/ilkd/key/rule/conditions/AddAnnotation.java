/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.conditions;

import java.util.Arrays;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.Annotation;
import de.uka.ilkd.key.java.ast.annotation.MarkerAnnotation;
import de.uka.ilkd.key.java.ast.expression.operator.New;
import de.uka.ilkd.key.java.ast.reference.TypeRef;
import de.uka.ilkd.key.java.ast.reference.TypeReference;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
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
 * that has an additional {@link Annotation} in its {@link TypeReference}.
 *
 * @author Daniel Grévent
 */
public final class AddAnnotation implements VariableCondition {
    private static final Logger LOGGER = LoggerFactory.getLogger(AddAnnotation.class);
    private static final Sort[] ALLOWED = {
        ProgramSVSort.SIMPLE_NEW,
        ProgramSVSort.LOCALVARIABLE, ProgramSVSort.VARIABLE
    };

    private final SchemaVariable read, store;
    private final String annot;

    /**
     * create an instance of the variable condition.
     *
     * @param store the {@link SchemaVariable} in which the new copy is stored
     * @param read the {@link SchemaVariable} that gets copied
     * @param annot the fully qualified name of the {@link Annotation} to add
     *
     * @throws IllegalArgumentException if `read` is not one of the {@link Sort}s
     *         in the `ALLOWED` array or the {@link Sort} of write is not compatible with
     *         that of `read`, so they do not correspond to the same kind of AST type.
     */
    public AddAnnotation(SchemaVariable store, SchemaVariable read, String annot) {
        if (!equivalent(store.sort(), read.sort())) {
            throw new IllegalArgumentException(
                "Expected left and right to have an equivalent sort!");
        }

        if (!Arrays.stream(ALLOWED).anyMatch(read.sort()::equals)) {
            throw new IllegalArgumentException(
                "Unsupported sort: " + read.sort() + ", supported: " +
                    Arrays.stream(ALLOWED).map(s -> s.toString()).reduce("",
                        (a, b) -> a + " " + b));
        }

        this.read = read;
        this.store = store;
        this.annot = annot;
    }

    /*
     * check that two sorts that are part of `ALLOWED` are correspond to a same
     * underlying type
     */
    private static boolean equivalent(Sort a, Sort b) {
        if (a == b)
            return true;
        if (a == ProgramSVSort.VARIABLE && b == ProgramSVSort.LOCALVARIABLE
                || b == ProgramSVSort.VARIABLE && a == ProgramSVSort.LOCALVARIABLE)
            return true;

        return false;
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

        Object inst = svInst.getInstantiation(read);

        Annotation annotation = build((Services) logicServices);
        if (inst instanceof ProgramVariable variable) {
            TypeReference tRef = addAnnotation(variable.getTypeReference(), annotation);
            LocationVariable replacement = newFromTypeRef(
                variable, (Services) logicServices, tRef);

            return matchCond.setInstantiations(
                svInst.add(store, replacement, logicServices));
        } else if (inst instanceof New cons) {
            TypeReference tRef = addAnnotation(cons.getTypeReference(), annotation);
            New replacement = newFromTypeRef(cons, tRef);

            return matchCond.setInstantiations(
                svInst.add(store, replacement, logicServices));
        }

        return matchCond;
    }

    private Annotation build(Services services) {
        return new MarkerAnnotation(services.getJavaInfo().getTypeByName(annot));
    }

    private static TypeReference addAnnotation(TypeReference tRef, Annotation annotation) {
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

    private static LocationVariable newFromTypeRef(ProgramVariable v, Services services,
            TypeReference tRef) {
        return new LocationVariable(
            services.getVariableNamer().getTemporaryNameProposal(v.name().toString()),
            tRef,
            v.getContainerType(),
            v.isStatic(),
            v.isModel(), v.isGhost(), v.isFinal());
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
