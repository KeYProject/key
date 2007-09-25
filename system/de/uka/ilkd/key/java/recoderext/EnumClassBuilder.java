// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2004 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.

package de.uka.ilkd.key.java.recoderext;

import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import org.apache.log4j.Logger;

import recoder.CrossReferenceServiceConfiguration;
import recoder.java.CompilationUnit;
import recoder.java.Expression;
import recoder.java.Identifier;
import recoder.java.JavaProgramFactory;
import recoder.java.declaration.*;
import recoder.java.reference.FieldReference;
import recoder.java.reference.TypeReference;
import recoder.java.reference.UncollatedReferenceQualifier;
import recoder.java.statement.Case;
import recoder.kit.ProblemReport;
import recoder.kit.TypeKit;

/**
 * 
 * This transformation is made to transform any found {@link EnumDeclaration}
 * into a corresponding {@link EnumClassDeclaration}.
 * 
 * <p>
 * Enums defined within another class are NOT converted as not supported yet by
 * KeY
 * 
 * @author mulbrich
 * @since 2006-11-20
 * @version 2006-11-21
 */
public class EnumClassBuilder extends RecoderModelTransformer {

    private static Logger logger = Logger.getLogger(EnumClassBuilder.class);

    /**
     * create a new instance that uses the given service configuration and works
     * on the given list of compilation units
     * 
     * @param services
     *            the cross referencing service configuration to be used
     * @param units
     *            the list of compilation units to be examined
     */
    public EnumClassBuilder(CrossReferenceServiceConfiguration services,
            List<CompilationUnit> units) {
        super(services, units);
    }

    /**
     * a mapping of enums to the newly created class declarations.
     */
    Map<EnumDeclaration, EnumClassDeclaration> substitutes =
            new HashMap<EnumDeclaration, EnumClassDeclaration>();
    
    /**
     * a mapping of constant references in switch-statements and their
     * substitutes.
     */
    Map<FieldReference, UncollatedReferenceQualifier> caseSubstitutes = 
            new HashMap<FieldReference, UncollatedReferenceQualifier>(); 

    /**
     * find all enum declarations and make their substitutes.
     * find all case usages of enum constants and make their substitutes.
     * 
     * @see recoder.kit.TwoPassTransformation#analyze()
     */
    @Override
    public ProblemReport analyze() {

        for (CompilationUnit unit : units) {
            for (TypeDeclaration td : unit.getDeclarations()) {
                if (td instanceof EnumDeclaration) {
                    EnumDeclaration ed = (EnumDeclaration) td;
                    addCases(ed);
                    EnumClassDeclaration ecd = new EnumClassDeclaration(ed);
                    substitutes.put(ed, ecd);
                    if (logger.isDebugEnabled()) {
                        for (MemberDeclaration m : ecd.getMembers()) {
                            logger.debug("Member of "
                                    + ecd.getIdentifier().getText() + ": "
                                    + m.toSource());
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
     * Use the cross reference property and find all case usages of enum constants
     * replace them by their fully qualified name, if they are not qualified.
     *  
     * @param ed the EnumDeclaration to search for.
     */
    private void addCases(EnumDeclaration ed) {
        
        for(EnumConstantDeclaration ecd : ed.getConstants()) {
            EnumConstantSpecification ecs = ecd.getEnumConstantSpecification();
                
            List<FieldReference> references = getCrossReferenceSourceInfo().getReferences(ecs);
            
            for (FieldReference fr : references) {
                if (fr.getASTParent() instanceof Case) {
                    TypeReference tyRef =
                            TypeKit.createTypeReference(
                                    JavaProgramFactory.getInstance(), ed);
                    UncollatedReferenceQualifier newCase =
                            new UncollatedReferenceQualifier(tyRef,
                                    ecs.getIdentifier().deepClone());
                    
                    caseSubstitutes.put(fr, newCase);
                }
            }
        
        }
    }

    /**
     * substitute EnumDeclarations by EnumClassDeclarations.
     * 
     * @see de.uka.ilkd.key.java.recoderext.RecoderModelTransformer#makeExplicit(recoder.java.declaration.TypeDeclaration)
     */
    protected void makeExplicit(TypeDeclaration td) {
        if (td instanceof EnumDeclaration) {
            EnumDeclaration ed = (EnumDeclaration) td;
            EnumClassDeclaration ecd = substitutes.get(ed);
            // new ObjectInspector(ed).showAndWait();
            if (ecd == null) {
                logger.error("There is no enum->class substitute for "
                        + td.getFullName());
            } else {
                replace(ed, ecd);
                assert ecd.getASTParent() != null : "No parent for "
                        + ecd.getIdentifier().getText();
            }
            
            // new ObjectInspector(ecd).showAndWait();
        }
        
    }

    /**
     * substitute all case statements that have been recorded earlier.
     * 
     * call super class to invoke "makeExplicit".
     * 
     * @see de.uka.ilkd.key.java.recoderext.RecoderModelTransformer#transform()
     */
    public void transform() {
        
        super.transform();
        
        for (Entry<FieldReference, UncollatedReferenceQualifier> entry : caseSubstitutes.entrySet()) {
            replace(entry.getKey(), entry.getValue());
        }
        
        getChangeHistory().updateModel();
    }
    
    

}
