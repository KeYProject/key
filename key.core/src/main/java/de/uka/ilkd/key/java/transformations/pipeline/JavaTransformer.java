// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
// Universitaet Koblenz-Landau, Germany
// Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
// Technical University Darmstadt, Germany
// Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.java.transformations.pipeline;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.TypeDeclaration;

import javax.annotation.Nonnull;

/**
 * The JavaDL requires some implicit fields, that are available in each
 * Java class. The name of the implicit fields starts usually with a dollar sign.
 * (in the age of recoder it was enclosed in angle brackets).
 * <p>
 * To access the fields in a uniform way, they are added as usual
 * fields to the classes, in particular this allows us to parse them in
 * easier.
 * For further information see also
 * <ul>
 * <li>{@link ImplicitFieldAdder}</li>
 * <li>{@link CreateObjectBuilder}</li>
 * <li>{@link PrepareObjectBuilder}</li>
 * </ul>
 * <p>
 * Performance of these classes was low, so information that is shared between
 * all instances of a transformation set has been outsourced to a transformation
 * cache.
 */
public abstract class JavaTransformer {
    /**
     * Further services and helper function for this pipeline step.
     */
    @Nonnull
    protected final TransformationPipelineServices services;

    /**
     * a cache object that stores information which is needed by
     * and common to many transformations. it includes the
     * compilation units, the declared classes, and information
     * for local classes.
     */
    @Nonnull
    protected final TransformationPipelineServices.TransformerCache cache;

    /**
     * creates a transformer for the recoder model
     *
     * @param services the CrossReferenceServiceConfiguration to access
     *                 model information
     */
    public JavaTransformer(@Nonnull TransformationPipelineServices services) {
        this.services = services;
        this.cache = services.getCache();
    }

    /**
     * The method is called for each type declaration of the compilation
     * unit and initiates the syntactical transformation. If you want to
     * descend in inner classes you have to implement the recursion by
     * yourself.
     */
    public abstract void apply(TypeDeclaration<?> td);

    public static RuntimeException reportError(Node node, String message, Object... args) {
        var path = node.findCompilationUnit().flatMap(CompilationUnit::getStorage)
                .map(it -> it.getPath().toString())
                .orElse("<unknown>");
        var line = node.getRange().map(it -> it.begin.line).orElse(-1);
        var col = node.getRange().map(it -> it.begin.column).orElse(-1);
        var pos = " at " + path + ":" + line + ":" + col;
        return new IllegalStateException(String.format(message + pos, args));
    }


    /*
     * protected class FinalOuterVarsCollector extends SourceVisitorExtended {
     *
     * private final HashMap<ReferenceType, List<Variable>> lc2fv;
     *
     * public FinalOuterVarsCollector() {
     * super();
     * lc2fv = cache.getLocalClass2FinalVarMapping();
     * }
     *
     * public void walk(SourceElement s) {
     * s.accept(this);
     * if (s instanceof Node) {
     * final Node pe = (Node) s;
     * for (int i = 0, sz = pe.getChildCount(); i < sz; i++) {
     * walk(pe.getChildAt(i));
     * }
     * }
     * }
     *
     * public void visitVariableReference(VariableReference vr) {
     * final DefaultCrossReferenceSourceInfo si = (DefaultCrossReferenceSourceInfo)
     * services.getSourceInfo();
     * final Variable v = si.getVariable(vr.getName(), vr);
     *
     * final ReferenceType containingReferenceTypeOfProgVarV = si.getContainingReferenceType((Node)
     * v);
     * ReferenceType ct = si.getContainingReferenceType(vr);
     * if (containingReferenceTypeOfProgVarV != ct &&
     * v instanceof VariableSpecification && !(v instanceof FieldSpecification)) {
     *
     * while (ct instanceof TypeDeclaration<?> && ct != containingReferenceTypeOfProgVarV) {
     * List<Variable> vars = lc2fv.get(ct);
     * if (vars == null) {
     * vars = new LinkedList<Variable>();
     * }
     * if (!vars.contains(v)) {
     * vars.add(v);
     * }
     * lc2fv.put(ct, vars);
     * ct = si.getContainingReferenceType(ct);
     * }
     * }
     * }
     * }
     */
}
