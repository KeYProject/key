/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.recoderext;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import de.uka.ilkd.key.util.Debug;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import recoder.CrossReferenceServiceConfiguration;
import recoder.convenience.TreeWalker;
import recoder.java.CompilationUnit;
import recoder.java.JavaProgramFactory;
import recoder.java.ProgramElement;
import recoder.java.declaration.*;
import recoder.java.reference.FieldReference;
import recoder.java.reference.TypeReference;
import recoder.java.reference.UncollatedReferenceQualifier;
import recoder.java.statement.Case;
import recoder.kit.ProblemReport;
import recoder.kit.TypeKit;

/**
 *
 * This transformation is made to transform any found {@link EnumDeclaration} into a corresponding
 * {@link EnumClassDeclaration}.
 *
 * @author mulbrich
 * @since 2006-11-20
 * @version 2006-11-21
 */
public class EnumClassBuilder extends RecoderModelTransformer {
    private static final Logger LOGGER = LoggerFactory.getLogger(EnumClassBuilder.class);

    /**
     * create a new instance that uses the given service configuration and works on the given list
     * of compilation units
     *
     * @param services the cross referencing service configuration to be used
     * @param cache a cache object that stores information which is needed by and common to many
     *        transformations. it includes the compilation units, the declared classes, and
     *        information for local classes.
     */
    public EnumClassBuilder(CrossReferenceServiceConfiguration services, TransformerCache cache) {
        super(services, cache);
    }

    /**
     * a mapping of enums to the newly created class declarations.
     */
    final Map<EnumDeclaration, EnumClassDeclaration> substitutes = new LinkedHashMap<>();

    /**
     * a mapping of constant references in switch-statements and their substitutes.
     */
    final Map<FieldReference, UncollatedReferenceQualifier> caseSubstitutes = new LinkedHashMap<>();

    /**
     * find all enum declarations and make their substitutes. find all case usages of enum constants
     * and make their substitutes.
     *
     * we may not the cache which buffers classes only not enums!
     *
     * @see recoder.kit.TwoPassTransformation#analyze()
     */
    @Override
    public ProblemReport analyze() {

        for (CompilationUnit unit : getUnits()) {
            TreeWalker tw = new TreeWalker(unit);
            while (tw.next()) {
                ProgramElement pe = tw.getProgramElement();
                if (pe instanceof EnumDeclaration ed) {
                    addCases(ed);
                    EnumClassDeclaration ecd = new EnumClassDeclaration(ed);
                    substitutes.put(ed, ecd);
                    if (Debug.ENABLE_DEBUG) {
                        for (MemberDeclaration m : ecd.getMembers()) {
                            LOGGER.debug(
                                "Member of " + ecd.getIdentifier().getText() + ": " + m.toSource());
                        }
                    }
                }
            }
        }
        return super.analyze();
    }

    /**
     * find enumconstants in case statements and mark them for substitution.
     *
     * Use the cross reference property and find all case usages of enum constants replace them by
     * their fully qualified name, if they are not qualified.
     *
     * @param ed the EnumDeclaration to search for.
     */
    private void addCases(EnumDeclaration ed) {

        for (EnumConstantDeclaration ecd : ed.getConstants()) {
            EnumConstantSpecification ecs = ecd.getEnumConstantSpecification();

            List<FieldReference> references = getCrossReferenceSourceInfo().getReferences(ecs);

            for (FieldReference fr : references) {
                if (fr.getASTParent() instanceof Case) {
                    TypeReference tyRef =
                        TypeKit.createTypeReference(JavaProgramFactory.getInstance(), ed);
                    UncollatedReferenceQualifier newCase =
                        new UncollatedReferenceQualifier(tyRef, ecs.getIdentifier().deepClone());

                    caseSubstitutes.put(fr, newCase);
                }
            }

        }
    }

    /**
     * substitute EnumDeclarations by EnumClassDeclarations.
     *
     * @see de.uka.ilkd.key.java.recoderext.RecoderModelTransformer#makeExplicit(recoder.java.declaration.TypeDeclaration)
     * @deprecated THIS DOES NOT WORK ANY MORE, SINCE THE CACHE ONLY CONSIDERS CLASSE TYPES, NOT
     *             ENUMS!
     */
    @Deprecated
    protected void makeExplicit(TypeDeclaration td) {}

    /**
     * substitute all case statements that have been recorded earlier.
     *
     * call super class to invoke "makeExplicit".
     *
     * @see de.uka.ilkd.key.java.recoderext.RecoderModelTransformer#transform()
     */
    @Override
    public void transform() {

        super.transform();

        for (EnumDeclaration ed : substitutes.keySet()) {
            EnumClassDeclaration ecd = substitutes.get(ed);
            if (ecd == null) {
                LOGGER.debug("There is no enum->class substitute for " + ed.getFullName());
            } else {
                replace(ed, ecd);
                assert ecd.getASTParent() != null
                        : "No parent for " + ecd.getIdentifier().getText();
            }
        }

        for (Entry<FieldReference, UncollatedReferenceQualifier> entry : caseSubstitutes
                .entrySet()) {
            replace(entry.getKey(), entry.getValue());
        }

        getChangeHistory().updateModel();
        cache.invalidateClasses();
    }



}
