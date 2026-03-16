/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang.jml;

import java.net.URI;
import java.util.*;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.TypeConverter;
import de.uka.ilkd.key.java.ast.*;
import de.uka.ilkd.key.java.ast.abstraction.ArrayType;
import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.ast.abstraction.Type;
import de.uka.ilkd.key.java.ast.declaration.*;
import de.uka.ilkd.key.java.ast.declaration.modifier.*;
import de.uka.ilkd.key.java.ast.reference.TypeReference;
import de.uka.ilkd.key.java.ast.statement.LabeledStatement;
import de.uka.ilkd.key.java.ast.statement.LoopStatement;
import de.uka.ilkd.key.java.ast.statement.MergePointStatement;
import de.uka.ilkd.key.ldt.FinalHeapResolution;
import de.uka.ilkd.key.logic.label.ParameterlessTermLabel;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.speclang.*;
import de.uka.ilkd.key.speclang.jml.pretranslation.*;
import de.uka.ilkd.key.speclang.jml.translation.JMLSpecFactory;
import de.uka.ilkd.key.speclang.njml.JmlFacade;
import de.uka.ilkd.key.speclang.njml.LabeledParserRuleContext;
import de.uka.ilkd.key.speclang.translation.SLTranslationException;
import de.uka.ilkd.key.speclang.translation.SLWarningException;

import org.key_project.util.collection.*;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;

import org.antlr.v4.runtime.ParserRuleContext;

import static de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLSpecCase.Clause.SIGNALS_ONLY;
import static de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLSpecCase.ClauseHd.*;
import static java.lang.String.format;

/**
 * Extracts JML class invariants and operation contracts from JML comments. This is the public
 * interface to the jml package. Note that internally, this class is highly similar to the class
 * java.recoderext.JMLTransformer; if you change one of these classes, you probably need to change
 * the other as well.
 */
public final class JMLSpecExtractor implements SpecExtractor {
    private static final String THROWABLE = "java.lang.Throwable";
    private static final String ERROR = "java.lang.Error";
    private static final String RUNTIME_EXCEPTION = "java.lang.RuntimeException";
    /** The default signals only clause for errors and runtime exceptions. **/
    private static final String DEFAULT_SIGNALS_ONLY =
        format("signals_only %s, %s;", ERROR, RUNTIME_EXCEPTION);
    /**
     * This is the term label for implicit specification clauses. This is important for
     * well-definedness checks. Hence, do not change its usages unless you understand and have
     * thought about the semantics of the corresponding well-definedness checks.
     **/
    private static final TermLabel IMPL_TERM_LABEL =
        ParameterlessTermLabel.IMPLICIT_SPECIFICATION_LABEL;
    private final Services services;
    private final JMLSpecFactory jsf;
    private ImmutableList<PositionedString> warnings = ImmutableSLList.nil();

    // -------------------------------------------------------------------------
    // constructors
    // -------------------------------------------------------------------------

    public JMLSpecExtractor(InitConfig initConfig) {
        FinalHeapResolution.rememberIfFinalEnabled(initConfig);
        this.services = initConfig.getServices();
        this.jsf = new JMLSpecFactory(services);
    }

    // includes unchecked exceptions (instances of Error or RuntimeException)
    // (see resolution to issue #1379)
    private ParserRuleContext getDefaultSignalsOnly(IProgramMethod pm) {
        if (pm.getThrown() == null) {
            return JmlFacade.parseClause(DEFAULT_SIGNALS_ONLY);
        }

        ImmutableArray<TypeReference> exceptions = pm.getThrown().getExceptions();

        if (exceptions == null) {
            return JmlFacade.parseClause(DEFAULT_SIGNALS_ONLY);
        }

        StringBuilder b = new StringBuilder();
        b.append(ERROR).append(", ").append(RUNTIME_EXCEPTION);

        for (int i = 0; i < exceptions.size(); i++) {
            if (services.getJavaInfo().isSubtype(exceptions.get(i).getKeYJavaType(),
                services.getJavaInfo().getKeYJavaType(THROWABLE))) {
                b.append(", ").append(exceptions.get(i).getKeYJavaType().getFullName());
            }
        }

        if (b.isEmpty()) {
            b.append("\\nothing");
        }
        return JmlFacade.parseClause("signals_only " + b + ";");
    }

    /**
     * creates a JML specification expressing that the given variable/field is not null and in case
     * of a reference array type that also its elements are non-null In case of implicit fields or
     * primitive typed fields/variables the empty set is returned
     *
     * @param varName the String specifying the variable/field name
     * @param kjt the KeYJavaType representing the variables/field declared type
     * @param isImplicitVar a boolean indicating if the field is an implicit one (in which case
     *        no
     * @param services the services object
     * @return set of formulas specifying non-nullity for field/variables
     */
    public static ImmutableSet<LabeledParserRuleContext> createNonNullPositionedString(
            String varName, KeYJavaType kjt, boolean isImplicitVar, Location location,
            Services services) {
        ImmutableSet<LabeledParserRuleContext> result = DefaultImmutableSet.nil();
        final Type varType = kjt.getJavaType();

        final TypeConverter typeConverter = services.getTypeConverter();
        if (typeConverter.isReferenceType(varType) && !isImplicitVar) {
            final int arrayDepth = arrayDepth(varType, services);

            // use special "deep" non null predicate (see bug #1392)
            // ... looks a bit like a hack with those DL escapes ...
            final String nonNullString =
                arrayDepth > 0 ? format("\\dl_nonNull(\\dl_heap(),%s,%d)", varName, arrayDepth)
                        : format("%s != null", varName);
            final ParserRuleContext ps =
                JmlFacade.parseExpr(new PositionedString(nonNullString, location));
            result = result.add(new LabeledParserRuleContext(ps, IMPL_TERM_LABEL));
        }
        return result;
    }


    /**
     * Get the depth for the nonNull predicate. The depth is 0 for non array types, its dimension
     * for reference array types, and its dimension -1 for array types with primitive base type.
     */
    public static int arrayDepth(Type type, Services services) {
        assert services != null;
        final TypeConverter tc = services.getTypeConverter();
        if (type instanceof ArrayType) {
            final int d = ((ArrayType) type).getDimension();
            while (type instanceof ArrayType) {
                type = ((ArrayType) type).getBaseType().getKeYJavaType().getJavaType();
            }
            return tc.isReferenceType(type) ? d : d - 1;
        } else {
            return 0;
        }
    }

    // -------------------------------------------------------------------------
    // public interface
    // -------------------------------------------------------------------------

    @Override
    public ImmutableSet<SpecificationElement> extractClassSpecs(KeYJavaType kjt)
            throws SLTranslationException {
        ImmutableSet<SpecificationElement> result = DefaultImmutableSet.nil();

        // primitive types have no class invariants
        if (!(kjt.getJavaType() instanceof TypeDeclaration td)) {
            return result;
        }

        // get type declaration, file name
        URI fileName = td.getPositionInfo().getURI().orElse(null);

        // add invariants for non_null fields
        for (MemberDeclaration member : td.getMembers()) {
            if (member instanceof FieldDeclaration) {
                VisibilityModifier visibility = null;
                for (Modifier mod : member.getModifiers()) {
                    if (mod instanceof VisibilityModifier) {
                        visibility = (VisibilityModifier) mod;
                        break;
                    }
                }
                // check for spec_* modifiers (bug #1280)
                if (JMLInfoExtractor.hasJMLModifier((FieldDeclaration) member,
                    Modifiers.JML_SPEC_PUBLIC.class)) {
                    visibility = new Public();
                } else if (JMLInfoExtractor.hasJMLModifier((FieldDeclaration) member,
                    Modifiers.JML_SPEC_PROTECTED.class)) {
                    visibility = new Protected();
                }

                for (FieldSpecification field : ((FieldDeclaration) member)
                        .getFieldSpecifications()) {
                    // add a static invariant for static fields
                    boolean isStatic = member.isStatic();

                    // add invariant only for fields of reference types
                    // and not for implicit fields.
                    if (!JMLInfoExtractor.isNullable((FieldDeclaration) member, td)) {
                        ImmutableSet<LabeledParserRuleContext> nonNullInvs =
                            createNonNullPositionedString(field.getProgramName(),
                                field.getProgramVariable().getKeYJavaType(),
                                field.isImplicit(),
                                new Location(fileName, member.getEndPosition()), services);
                        for (LabeledParserRuleContext classInv : nonNullInvs) {
                            final ClassInvariant jmlClassInvariant =
                                jsf.createJMLClassInvariant(kjt, visibility, isStatic, classInv);
                            result = result.add(jmlClassInvariant);
                        }
                    }
                }
            }
        }


        var constructs = td.getAttachedJml();
        // create class invs out of textual constructs, add them to result
        for (TextualJMLConstruct c : constructs) {
            try {
                switch (c) {
                    case TextualJMLClassInv textualInv -> {
                        ClassInvariant inv = jsf.createJMLClassInvariant(kjt, textualInv);
                        result = result.add(inv);
                    }
                    case TextualJMLInitially textualRep -> {
                        InitiallyClause inc = jsf.createJMLInitiallyClause(kjt, textualRep);
                        result = result.add(inc);
                    }
                    case TextualJMLRepresents textualRep -> {
                        ClassAxiom rep = jsf.createJMLRepresents(kjt, textualRep);
                        result = result.add(rep);
                    }
                    case TextualJMLDepends textualDep -> {
                        Contract depContract = jsf.createJMLDependencyContract(kjt, textualDep);
                        result = result.add(depContract);
                    }
                    case TextualJMLClassAxiom textualJMLClassAxiom -> {
                        ClassAxiom ax = jsf.createJMLClassAxiom(kjt, textualJMLClassAxiom);
                        result = result.add(ax);
                    }
                    case null, default -> {
                    }
                    // DO NOTHING
                    // There may be other kinds of JML constructs which are
                    // not specifications.
                }
            } catch (SLWarningException e) {
                warnings = warnings.append(e.getWarning());
            }
        }
        return result;
    }

    @Override
    public List<SpecificationElement> extractMethodSpecs(IProgramMethod pm)
            throws SLTranslationException {
        return extractMethodSpecs(pm, true);
    }

    /**
     * Extracts method specifications (i.e., contracts) from Java+JML input.
     *
     * @param pm method to extract for
     * @param addInvariant whether to add <i>static</i> invariants to pre- and post-conditions
     */
    @Override
    public List<SpecificationElement> extractMethodSpecs(IProgramMethod pm, boolean addInvariant)
            throws SLTranslationException {
        List<SpecificationElement> result = new ArrayList<>();

        // get type declaration, file name
        TypeDeclaration td = (TypeDeclaration) pm.getContainerType().getJavaType();
        URI fileName = td != null ? td.getPositionInfo().getURI().orElse(null) : null;

        // determine purity
        final boolean isStrictlyPure = JMLInfoExtractor.isStrictlyPure(pm);
        final boolean isPure = JMLInfoExtractor.isPure(pm);
        final boolean isHelper = JMLInfoExtractor.isHelper(pm);

        // get textual JML constructs
        ImmutableList<TextualJMLConstruct> constructs = pm.getMethodDeclaration().getAttachedJml();

        ParserRuleContext modelMethodDefinition = null;
        for (var c : constructs) {
            if (c instanceof TextualJMLMethodDecl m) {
                if (pm.getMethodDeclaration().containsModifier(Model.class)) {
                    modelMethodDefinition = m.getMethodDefinition();
                    break;
                }
            }
        }

        // Model method without specification. We need to create a specCase
        // to attach the AXIOMS clase for its definition.
        if (modelMethodDefinition != null && constructs.size() == 1) {
            TextualJMLSpecCase specCase =
                new TextualJMLSpecCase(ImmutableList.of(), Behavior.MODEL_BEHAVIOR);
            constructs = constructs.append(specCase);
        }

        for (var c : constructs) {
            if (c instanceof TextualJMLSpecCase specCase) {
                specCase = specCase.copy();

                if (modelMethodDefinition != null) {
                    specCase.addClause(AXIOMS, null, modelMethodDefinition);
                }

                // add purity. Strict purity overrides purity.
                if (isStrictlyPure || pm.isModel()) {
                    for (LocationVariable heap : HeapContext.getModifiableHeaps(services, false)) {
                        specCase.addClause(ASSIGNABLE, heap.name(),
                            JmlFacade.parseExpr("\\strictly_nothing"));
                    }
                } else if (isPure) {
                    for (LocationVariable heap : HeapContext.getModifiableHeaps(services, false)) {
                        specCase.addClause(ASSIGNABLE, heap.name(),
                            JmlFacade.parseExpr("\\nothing"));
                    }
                }

                // add invariants
                if (!isHelper && pm.getStateCount() > 0 && (!pm.isStatic() || addInvariant)) {
                    // for a static method translate \inv once again, otherwise use
                    // the internal symbol
                    final String invString = pm.isStatic() ? "\\inv" : "<$inv>";
                    final String invFreeString = pm.isStatic() ? "\\inv_free" : "<$inv_free>";

                    KeYJavaType classType = pm.getContainerType();
                    boolean hasFreeInvariant = services.getSpecificationRepository()
                            .getClassInvariants(classType).stream()
                            .anyMatch(ClassInvariant::isFree);

                    if (!pm.isConstructor()) {
                        specCase.addClause(REQUIRES, new LabeledParserRuleContext(
                            JmlFacade.parseExpr(invString), IMPL_TERM_LABEL));
                        if (hasFreeInvariant) {
                            specCase.addClause(REQUIRES_FREE, new LabeledParserRuleContext(
                                JmlFacade.parseExpr(invFreeString), IMPL_TERM_LABEL));
                        }
                    } else if (addInvariant) {
                        // add static invariant to constructor's precondition
                        specCase.addClause(REQUIRES, new LabeledParserRuleContext(
                            JmlFacade.parseExpr(format("%s.\\inv", pm.getName())),
                            IMPL_TERM_LABEL));
                        if (hasFreeInvariant) {
                            specCase.addClause(REQUIRES_FREE, new LabeledParserRuleContext(
                                JmlFacade.parseExpr(format("%s.\\inv_free", pm.getName())),
                                IMPL_TERM_LABEL));
                        }
                    }
                    if (specCase.getBehavior() != Behavior.EXCEPTIONAL_BEHAVIOR) {
                        specCase.addClause(ENSURES, new LabeledParserRuleContext(
                            JmlFacade.parseExpr(invString), IMPL_TERM_LABEL));
                        if (hasFreeInvariant) {
                            specCase.addClause(ENSURES_FREE, new LabeledParserRuleContext(
                                JmlFacade.parseExpr(invFreeString), IMPL_TERM_LABEL));
                        }

                    }
                    if (specCase.getBehavior() != Behavior.NORMAL_BEHAVIOR && !pm.isModel()) {
                        specCase.addClause(TextualJMLSpecCase.Clause.SIGNALS,
                            new LabeledParserRuleContext(
                                JmlFacade.parseClause(
                                    format("signals (Throwable e) %s;", invString)),
                                IMPL_TERM_LABEL));

                    }
                }

                // add non-null preconditions
                for (int j = 0, n = pm.getParameterDeclarationCount(); j < n; j++) {
                    final VariableSpecification paramDecl =
                        pm.getParameterDeclarationAt(j).getVariableSpecification();
                    if (!JMLInfoExtractor.parameterIsNullable(pm, j)) {
                        // no additional precondition for primitive types!
                        // createNonNullPos... takes care of that
                        final ImmutableSet<LabeledParserRuleContext> nonNullParams =
                            createNonNullPositionedString(paramDecl.getName(),
                                paramDecl.getProgramVariable().getKeYJavaType(), false,
                                new Location(fileName,
                                    pm.getStartPosition()),
                                services);
                        for (LabeledParserRuleContext nonNull : nonNullParams) {
                            specCase.addClause(REQUIRES, nonNull);
                        }
                    }
                }

                // add non-null postcondition
                KeYJavaType resultType = pm.getReturnType();

                if (!pm.isVoid() && !pm.isConstructor() && !JMLInfoExtractor.resultIsNullable(pm)
                        && specCase.getBehavior() != Behavior.EXCEPTIONAL_BEHAVIOR) {
                    final ImmutableSet<LabeledParserRuleContext> resultNonNull =
                        createNonNullPositionedString("\\result", resultType, false,
                            new Location(fileName,
                                pm.getStartPosition()),
                            services);
                    for (LabeledParserRuleContext nonNull : resultNonNull) {
                        specCase.addClause(ENSURES, nonNull);
                    }
                }

                // add implicit signals-only if omitted
                if (specCase.getSignalsOnly().isEmpty()
                        && specCase.getBehavior() != Behavior.NORMAL_BEHAVIOR && !pm.isModel()) {
                    specCase.addClause(SIGNALS_ONLY, getDefaultSignalsOnly(pm));
                }

                // translate contract
                try {
                    ImmutableSet<Contract> contracts =
                        jsf.createJMLOperationContracts(pm, specCase);
                    for (Contract contract : contracts) {
                        result.add(contract);
                    }
                } catch (SLWarningException e) {
                    warnings = warnings.append(e.getWarning());
                }
            }
        }
        return result;
    }

    @Override
    public ImmutableSet<BlockContract> extractBlockContracts(final IProgramMethod method,
            final StatementBlock block) throws SLTranslationException {
        return createBlockContracts(method, new LinkedList<>(), block);
    }

    @Override
    public ImmutableSet<BlockContract> extractBlockContracts(final IProgramMethod method,
            final LabeledStatement labeled) throws SLTranslationException {
        final List<Label> labels = new LinkedList<>();
        labels.add(labeled.getLabel());
        Statement nextNonLabeled = labeled.getBody();
        while (nextNonLabeled instanceof LabeledStatement currentLabeled) {
            labels.add(currentLabeled.getLabel());
            nextNonLabeled = currentLabeled.getBody();
        }
        if (nextNonLabeled instanceof StatementBlock) {
            return createBlockContracts(method, labels, (StatementBlock) nextNonLabeled);
        } else {
            return DefaultImmutableSet.nil();
        }
    }

    @Override
    public ImmutableSet<LoopContract> extractLoopContracts(final IProgramMethod method,
            final LoopStatement loop) throws SLTranslationException {
        return createLoopContracts(method, new LinkedList<>(), loop);
    }

    @Override
    public ImmutableSet<LoopContract> extractLoopContracts(final IProgramMethod method,
            final StatementBlock block) throws SLTranslationException {
        return createLoopContracts(method, new LinkedList<>(), block);
    }

    @Override
    public ImmutableSet<LoopContract> extractLoopContracts(final IProgramMethod method,
            final LabeledStatement labeled) throws SLTranslationException {
        final List<Label> labels = new LinkedList<>();
        labels.add(labeled.getLabel());
        Statement nextNonLabeled = labeled.getBody();
        while (nextNonLabeled instanceof LabeledStatement currentLabeled) {
            labels.add(currentLabeled.getLabel());
            nextNonLabeled = currentLabeled.getBody();
        }
        if (nextNonLabeled instanceof StatementBlock) {
            return createLoopContracts(method, labels, (StatementBlock) nextNonLabeled);
        } else if (nextNonLabeled instanceof LoopStatement) {
            return createLoopContracts(method, labels, (LoopStatement) nextNonLabeled);
        } else {
            return DefaultImmutableSet.nil();
        }
    }

    @Override
    public ImmutableSet<MergeContract> extractMergeContracts(IProgramMethod method,
            MergePointStatement mps, ImmutableList<LocationVariable> methodParams)
            throws SLTranslationException {
        // In cases of specifications immediately following each other (like a
        // merge_point and a block contract / loop invariant), it might happen
        // that we're passed multiple constructs here. Therefore, we filter the
        // merge point specific parts here
        var constructs = mps.getAttachedJml();
        for (var construct : constructs) {
            if (construct instanceof TextualJMLMergePointDecl m) {
                return jsf.createJMLMergeContracts(method, mps, m);
            }
        }
        return ImmutableSet.empty();
    }

    private ImmutableSet<BlockContract> createBlockContracts(final IProgramMethod method,
            final List<Label> labels, final StatementBlock block)
            throws SLTranslationException {
        ImmutableSet<BlockContract> result = DefaultImmutableSet.nil();
        // For some odd reason every comment block appears twice; thus we remove
        // duplicates.
        final TextualJMLConstruct[] constructs =
            block.getAttachedJml().toArray(new TextualJMLConstruct[0]);
        for (int i = constructs.length - 1; i >= 0
                && constructs[i] instanceof TextualJMLSpecCase specificationCase; i--) {
            try {
                result = result.union(
                    jsf.createJMLBlockContracts(method, labels, block, specificationCase));
            } catch (final SLWarningException exception) {
                warnings = warnings.append(exception.getWarning());
            }
        }
        return result;
    }

    private ImmutableSet<LoopContract> createLoopContracts(final IProgramMethod method,
            final List<Label> labels, final LoopStatement loop)
            throws SLTranslationException {
        ImmutableSet<LoopContract> result = DefaultImmutableSet.nil();
        // For some odd reason every comment block appears twice; thus we remove
        // duplicates.
        final TextualJMLConstruct[] constructs =
            loop.getAttachedJml().toArray(new TextualJMLConstruct[0]);
        for (int i = constructs.length - 1; i >= 0
                && constructs[i] instanceof TextualJMLSpecCase specificationCase; i--) {
            try {
                result = result
                        .union(jsf.createJMLLoopContracts(method, labels, loop, specificationCase));
            } catch (final SLWarningException exception) {
                warnings = warnings.append(exception.getWarning());
            }
        }
        return result;
    }

    private ImmutableSet<LoopContract> createLoopContracts(final IProgramMethod method,
            final List<Label> labels, final StatementBlock block)
            throws SLTranslationException {
        ImmutableSet<LoopContract> result = DefaultImmutableSet.nil();
        // For some odd reason every comment block appears twice; thus we remove
        // duplicates.
        final TextualJMLConstruct[] constructs =
            block.getAttachedJml().toArray(new TextualJMLConstruct[0]);
        // parseMethodLevelComments(removeDuplicates(comments), getFileName(method));
        for (int i = constructs.length - 1; i >= 0
                && constructs[i] instanceof TextualJMLSpecCase specificationCase; i--) {
            try {
                result = result.union(
                    jsf.createJMLLoopContracts(method, labels, block, specificationCase));
            } catch (final SLWarningException exception) {
                warnings = warnings.append(exception.getWarning());
            }
        }
        return result;
    }

    @Override
    public LoopSpecification extractLoopInvariant(IProgramMethod pm, LoopStatement loop) {
        LoopSpecification result = null;

        ImmutableList<TextualJMLConstruct> constructs = loop.getAttachedJml();

        // create JML loop invariant out of last construct
        if (constructs.isEmpty()) {
            return result;
        }
        TextualJMLConstruct c = constructs.take(constructs.size() - 1).head();
        if (c instanceof TextualJMLLoopSpec textualLoopSpec) {
            result = jsf.createJMLLoopInvariant(pm, loop, textualLoopSpec);

            // Check that a decreases clause exists
            if (result.getInternalVariant() == null) {
                PositionInfo info = loop.getPositionInfo();
                warnings = warnings.append(
                    new PositionedString(
                        "Missing \"decreases\" for loop invariant. " +
                            "Termination of this loop will not be provable.",
                        new Location(info.getURI().orElse(null), info.getStartPosition())));
            }
        }
        return result;
    }

    @Override
    public ImmutableList<PositionedString> getWarnings() {
        return warnings;
    }

    @Override
    public Contract createDefaultContract(IProgramMethod method, boolean useSoundDefault) {
        return jsf.createDefaultContract(method, useSoundDefault);
    }
}
