/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.speclang.jml;

import java.net.URI;
import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.TypeConverter;
import de.uka.ilkd.key.java.ast.Label;
import de.uka.ilkd.key.java.ast.PositionInfo;
import de.uka.ilkd.key.java.ast.Statement;
import de.uka.ilkd.key.java.ast.StatementBlock;
import de.uka.ilkd.key.java.ast.abstraction.ArrayType;
import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.ast.abstraction.Type;
import de.uka.ilkd.key.java.ast.declaration.*;
import de.uka.ilkd.key.java.ast.declaration.ModifierKind;
import de.uka.ilkd.key.java.ast.statement.LabeledStatement;
import de.uka.ilkd.key.java.ast.statement.LoopStatement;
import de.uka.ilkd.key.java.ast.statement.MergePointStatement;
import de.uka.ilkd.key.ldt.FinalHeapResolution;
import de.uka.ilkd.key.logic.label.ParameterlessTermLabel;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.speclang.*;
import de.uka.ilkd.key.speclang.jml.translation.JMLSpecFactory;
import de.uka.ilkd.key.speclang.njml.JmlFacade;
import de.uka.ilkd.key.speclang.njml.LabeledParserRuleContext;
import de.uka.ilkd.key.speclang.translation.SLTranslationException;
import de.uka.ilkd.key.speclang.translation.SLWarningException;

import org.key_project.util.collection.*;
import org.key_project.util.parsing.Location;

import com.github.javaparser.ast.jml.body.JmlClassAccessibleDeclaration;
import com.github.javaparser.ast.jml.body.JmlClassExprDeclaration;
import com.github.javaparser.ast.jml.body.JmlRepresentsDeclaration;
import com.github.javaparser.ast.jml.clauses.ContractType;
import com.github.javaparser.ast.jml.clauses.JmlContract;
import com.github.javaparser.ast.key.KeyMergePointStmt;

import static java.lang.String.format;

/**
 * Extracts JML class invariants and operation contracts from the JMLtk AST (attached as
 * {@link JmlSpec} to the Java AST). This is the public interface to the jml package.
 * <p>
 * The actual translation into KeY specifications is delegated to the {@link JMLSpecFactory}; this
 * class only distributes the attached JML constructs to the right factory methods.
 */
public final class JMLSpecExtractor implements SpecExtractor {

    private final Services services;
    private final JMLSpecFactory jsf;
    private ImmutableList<PositionedString> warnings = ImmutableList.nil();

    /**
     * This is the term label for implicit specification clauses. This is important for
     * well-definedness checks. Hence, do not change its usages unless you understand and have
     * thought about the semantics of the corresponding well-definedness checks.
     **/
    private static final TermLabel IMPL_TERM_LABEL =
        ParameterlessTermLabel.IMPLICIT_SPECIFICATION_LABEL;

    // -------------------------------------------------------------------------
    // constructors
    // -------------------------------------------------------------------------

    public JMLSpecExtractor(InitConfig initConfig) {
        FinalHeapResolution.rememberIfFinalEnabled(initConfig);
        this.services = initConfig.getServices();
        this.jsf = new JMLSpecFactory(services);
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
            final var ps = JmlFacade.parseExpr(new PositionedString(nonNullString, location));
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
                ModifierKind visibility = null;
                for (Modifier mod : member.getModifiers()) {
                    final ModifierKind modKind = mod.getKind();
                    if (modKind.isVisibility()) {
                        visibility = modKind;
                        break;
                    }
                }
                // check for spec_* modifiers (bug #1280)
                if (JMLInfoExtractor.hasJMLModifier((FieldDeclaration) member,
                    ModifierKind.JML_SPEC_PUBLIC)) {
                    visibility = ModifierKind.PUBLIC;
                } else if (JMLInfoExtractor.hasJMLModifier((FieldDeclaration) member,
                    ModifierKind.JML_SPEC_PROTECTED)) {
                    visibility = ModifierKind.PROTECTED;
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

        // create class specifications out of the attached JML constructs and add them to result
        var constructs = td.getAttachedJml();
        for (JmlSpec c : constructs) {
            try {
                if (c.node() instanceof JmlClassExprDeclaration decl) {
                    switch (decl.getKind()) {
                        case INVARIANT, INVARIANT_FREE -> {
                            ClassInvariant inv = jsf.createJMLClassInvariant(kjt, c);
                            result = result.add(inv);
                        }
                        case INITIALLY -> {
                            InitiallyClause inc = jsf.createJMLInitiallyClause(kjt, c);
                            result = result.add(inc);
                        }
                        case AXIOM -> {
                            ClassAxiom ax = jsf.createJMLClassAxiom(kjt, c);
                            result = result.add(ax);
                        }
                        default -> {
                            // DO NOTHING (there may be other class level constructs which are
                            // not specifications, e.g. invariants_redundantly)
                        }
                    }
                } else if (c.node() instanceof JmlRepresentsDeclaration) {
                    ClassAxiom rep = jsf.createJMLRepresents(kjt, c);
                    result = result.add(rep);
                } else if (c.node() instanceof JmlClassAccessibleDeclaration) {
                    Contract depContract = jsf.createJMLDependencyContract(kjt, c);
                    result = result.add(depContract);
                }
                // DO NOTHING for other JML constructs (JmlMethodDeclaration, JmlFieldDeclaration)
                // which are not specifications themselves.
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

        // get the attached JML constructs
        ImmutableList<JmlSpec> constructs = pm.getMethodDeclaration().getAttachedJml();

        for (JmlSpec c : constructs) {
            try {
                ImmutableSet<Contract> contracts =
                    jsf.createJMLOperationContracts(pm, c, addInvariant);
                for (Contract contract : contracts) {
                    result.add(contract);
                }
            } catch (SLWarningException e) {
                warnings = warnings.append(e.getWarning());
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
            if (construct.node() instanceof KeyMergePointStmt) {
                return jsf.createJMLMergeContracts(method, mps, construct);
            }
        }
        return ImmutableSet.empty();
    }

    private ImmutableSet<BlockContract> createBlockContracts(final IProgramMethod method,
            final List<Label> labels, final StatementBlock block)
            throws SLTranslationException {
        ImmutableSet<BlockContract> result = DefaultImmutableSet.nil();
        for (JmlSpec construct : block.getAttachedJml()) {
            if (construct.node() instanceof JmlContract contract
                    && contract.getType() != ContractType.LOOP
                    && contract.getType() != ContractType.LOOP_INV) {
                try {
                    result = result
                            .union(jsf.createJMLBlockContracts(method, labels, block, construct));
                } catch (final SLWarningException exception) {
                    warnings = warnings.append(exception.getWarning());
                }
            }
        }
        return result;
    }

    private ImmutableSet<LoopContract> createLoopContracts(final IProgramMethod method,
            final List<Label> labels, final LoopStatement loop)
            throws SLTranslationException {
        ImmutableSet<LoopContract> result = DefaultImmutableSet.nil();
        for (JmlSpec construct : loop.getAttachedJml()) {
            if (construct.node() instanceof JmlContract contract
                    && contract.getType() == ContractType.LOOP) {
                try {
                    result = result
                            .union(jsf.createJMLLoopContracts(method, labels, loop, construct));
                } catch (final SLWarningException exception) {
                    warnings = warnings.append(exception.getWarning());
                }
            }
        }
        return result;
    }

    private ImmutableSet<LoopContract> createLoopContracts(final IProgramMethod method,
            final List<Label> labels, final StatementBlock block)
            throws SLTranslationException {
        ImmutableSet<LoopContract> result = DefaultImmutableSet.nil();
        for (JmlSpec construct : block.getAttachedJml()) {
            if (construct.node() instanceof JmlContract contract
                    && contract.getType() == ContractType.LOOP) {
                try {
                    result = result
                            .union(jsf.createJMLLoopContracts(method, labels, block, construct));
                } catch (final SLWarningException exception) {
                    warnings = warnings.append(exception.getWarning());
                }
            }
        }
        return result;
    }

    @Override
    public LoopSpecification extractLoopInvariant(IProgramMethod pm, LoopStatement loop) {
        LoopSpecification result = null;

        ImmutableList<JmlSpec> constructs = loop.getAttachedJml();

        // create JML loop invariant out of the last loop invariant contract
        for (int i = constructs.size() - 1; i >= 0; i--) {
            JmlSpec c = constructs.get(i);
            if (c.node() instanceof JmlContract contract
                    && contract.getType() == ContractType.LOOP_INV) {
                result = jsf.createJMLLoopInvariant(pm, loop, c);

                // Check that a decreases clause exists
                if (result.getInternalVariant() == null) {
                    PositionInfo info = loop.getPositionInfo();
                    warnings = warnings.append(
                        new PositionedString(
                            "Missing \"decreases\" for loop invariant. " +
                                "Termination of this loop will not be provable.",
                            new Location(info.getURI().orElse(null), info.getStartPosition())));
                }
                break;
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
