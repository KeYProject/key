/*******************************************************************************
 * Copyright (c) 2013 Karlsruhe Institute of Technology, Germany 
 *                    Technical University Darmstadt, Germany
 *                    Chalmers University of Technology, Sweden
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Technical University Darmstadt - initial API and implementation and/or initial documentation
 *******************************************************************************/

package de.hentschel.visualdbc.dbcmodel.diagram.providers;

import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.emf.ecore.EAttribute;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.gmf.runtime.common.core.service.AbstractProvider;
import org.eclipse.gmf.runtime.common.core.service.IOperation;
import org.eclipse.gmf.runtime.common.ui.services.parser.GetParserOperation;
import org.eclipse.gmf.runtime.common.ui.services.parser.IParser;
import org.eclipse.gmf.runtime.common.ui.services.parser.IParserProvider;
import org.eclipse.gmf.runtime.common.ui.services.parser.ParserService;
import org.eclipse.gmf.runtime.emf.type.core.IElementType;
import org.eclipse.gmf.runtime.emf.ui.services.parser.ParserHintAdapter;
import org.eclipse.gmf.runtime.notation.View;

import de.hentschel.visualdbc.dbcmodel.DbcmodelPackage;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbCAxiomContractDepEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbCAxiomContractNameEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbCAxiomContractPreEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcAttributeEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcAttributeNameTypeEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcAxiomDefinitionEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcAxiomNameEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcClassName2EditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcClassNameEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcConstructorSignatureEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcEnumLiteralEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcEnumLiteralNameEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcEnumName2EditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcEnumNameEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcInterfaceName2EditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcInterfaceNameEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcInvariantNameEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcInvariantTextEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcMethodSignatureReturnTypeEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcOperationContractNameEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcOperationContractPostEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcOperationContractPreEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcPackageName2EditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcPackageNameEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcProofObligation2EditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcProofObligationEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcProofReferenceKindEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.parsers.MessageFormatParser;
import de.hentschel.visualdbc.dbcmodel.diagram.part.DbCVisualIDRegistry;

/**
 * @generated
 */
public class DbCParserProvider extends AbstractProvider implements
      IParserProvider {

   /**
    * @generated
    */
   private IParser dbcPackageName_5042Parser;

   /**
    * @generated
    */
   private IParser getDbcPackageName_5042Parser() {
      if (dbcPackageName_5042Parser == null) {
         EAttribute[] features = new EAttribute[] { DbcmodelPackage.eINSTANCE
               .getDbcPackage_Name() };
         MessageFormatParser parser = new MessageFormatParser(features);
         dbcPackageName_5042Parser = parser;
      }
      return dbcPackageName_5042Parser;
   }

   /**
    * @generated
    */
   private IParser dbcInterfaceName_5049Parser;

   /**
    * @generated
    */
   private IParser getDbcInterfaceName_5049Parser() {
      if (dbcInterfaceName_5049Parser == null) {
         EAttribute[] features = new EAttribute[] { DbcmodelPackage.eINSTANCE
               .getAbstractDbcType_Name() };
         MessageFormatParser parser = new MessageFormatParser(features);
         dbcInterfaceName_5049Parser = parser;
      }
      return dbcInterfaceName_5049Parser;
   }

   /**
    * @generated
    */
   private IParser dbcClassName_5050Parser;

   /**
    * @generated
    */
   private IParser getDbcClassName_5050Parser() {
      if (dbcClassName_5050Parser == null) {
         EAttribute[] features = new EAttribute[] { DbcmodelPackage.eINSTANCE
               .getAbstractDbcType_Name() };
         MessageFormatParser parser = new MessageFormatParser(features);
         dbcClassName_5050Parser = parser;
      }
      return dbcClassName_5050Parser;
   }

   /**
    * @generated
    */
   private IParser dbcEnumName_5051Parser;

   /**
    * @generated
    */
   private IParser getDbcEnumName_5051Parser() {
      if (dbcEnumName_5051Parser == null) {
         EAttribute[] features = new EAttribute[] { DbcmodelPackage.eINSTANCE
               .getAbstractDbcType_Name() };
         MessageFormatParser parser = new MessageFormatParser(features);
         dbcEnumName_5051Parser = parser;
      }
      return dbcEnumName_5051Parser;
   }

   /**
    * @generated
    */
   private IParser dbcProofObligation_5053Parser;

   /**
    * @generated
    */
   private IParser getDbcProofObligation_5053Parser() {
      if (dbcProofObligation_5053Parser == null) {
         EAttribute[] features = new EAttribute[] { DbcmodelPackage.eINSTANCE
               .getDbcProof_Obligation() };
         MessageFormatParser parser = new MessageFormatParser(features);
         dbcProofObligation_5053Parser = parser;
      }
      return dbcProofObligation_5053Parser;
   }

   /**
    * @generated
    */
   private IParser dbcPackageName_5041Parser;

   /**
    * @generated
    */
   private IParser getDbcPackageName_5041Parser() {
      if (dbcPackageName_5041Parser == null) {
         EAttribute[] features = new EAttribute[] { DbcmodelPackage.eINSTANCE
               .getDbcPackage_Name() };
         MessageFormatParser parser = new MessageFormatParser(features);
         dbcPackageName_5041Parser = parser;
      }
      return dbcPackageName_5041Parser;
   }

   /**
    * @generated
    */
   private IParser dbcClassName_5048Parser;

   /**
    * @generated
    */
   private IParser getDbcClassName_5048Parser() {
      if (dbcClassName_5048Parser == null) {
         EAttribute[] features = new EAttribute[] { DbcmodelPackage.eINSTANCE
               .getAbstractDbcType_Name() };
         MessageFormatParser parser = new MessageFormatParser(features);
         dbcClassName_5048Parser = parser;
      }
      return dbcClassName_5048Parser;
   }

   /**
    * @generated
    */
   private IParser dbcInterfaceName_5047Parser;

   /**
    * @generated
    */
   private IParser getDbcInterfaceName_5047Parser() {
      if (dbcInterfaceName_5047Parser == null) {
         EAttribute[] features = new EAttribute[] { DbcmodelPackage.eINSTANCE
               .getAbstractDbcType_Name() };
         MessageFormatParser parser = new MessageFormatParser(features);
         dbcInterfaceName_5047Parser = parser;
      }
      return dbcInterfaceName_5047Parser;
   }

   /**
    * @generated
    */
   private IParser dbcEnumName_5046Parser;

   /**
    * @generated
    */
   private IParser getDbcEnumName_5046Parser() {
      if (dbcEnumName_5046Parser == null) {
         EAttribute[] features = new EAttribute[] { DbcmodelPackage.eINSTANCE
               .getAbstractDbcType_Name() };
         MessageFormatParser parser = new MessageFormatParser(features);
         dbcEnumName_5046Parser = parser;
      }
      return dbcEnumName_5046Parser;
   }

   /**
    * @generated
    */
   private IParser dbcProofObligation_5052Parser;

   /**
    * @generated
    */
   private IParser getDbcProofObligation_5052Parser() {
      if (dbcProofObligation_5052Parser == null) {
         EAttribute[] features = new EAttribute[] { DbcmodelPackage.eINSTANCE
               .getDbcProof_Obligation() };
         MessageFormatParser parser = new MessageFormatParser(features);
         dbcProofObligation_5052Parser = parser;
      }
      return dbcProofObligation_5052Parser;
   }

   /**
    * @generated
    */
   private IParser dbcInvariantName_5054Parser;

   /**
    * @generated
    */
   private IParser getDbcInvariantName_5054Parser() {
      if (dbcInvariantName_5054Parser == null) {
         EAttribute[] features = new EAttribute[] { DbcmodelPackage.eINSTANCE
               .getAbstractDbcSpecification_Name() };
         MessageFormatParser parser = new MessageFormatParser(features);
         dbcInvariantName_5054Parser = parser;
      }
      return dbcInvariantName_5054Parser;
   }

   /**
    * @generated
    */
   private IParser dbcInvariantCondition_5055Parser;

   /**
    * @generated
    */
   private IParser getDbcInvariantCondition_5055Parser() {
      if (dbcInvariantCondition_5055Parser == null) {
         EAttribute[] features = new EAttribute[] { DbcmodelPackage.eINSTANCE
               .getDbcInvariant_Condition() };
         MessageFormatParser parser = new MessageFormatParser(features);
         dbcInvariantCondition_5055Parser = parser;
      }
      return dbcInvariantCondition_5055Parser;
   }

   /**
    * @generated
    */
   private IParser dbcAttributeNameType_5061Parser;

   /**
    * @generated
    */
   private IParser getDbcAttributeNameType_5061Parser() {
      if (dbcAttributeNameType_5061Parser == null) {
         EAttribute[] features = new EAttribute[] {
               DbcmodelPackage.eINSTANCE.getDbcAttribute_Name(),
               DbcmodelPackage.eINSTANCE.getDbcAttribute_Type() };
         MessageFormatParser parser = new MessageFormatParser(features);
         parser.setViewPattern("{0} : {1}"); //$NON-NLS-1$
         parser.setEditorPattern("{0} : {1}"); //$NON-NLS-1$
         parser.setEditPattern("{0} : {1}"); //$NON-NLS-1$
         dbcAttributeNameType_5061Parser = parser;
      }
      return dbcAttributeNameType_5061Parser;
   }

   /**
    * @generated
    */
   private IParser dbcMethodSignatureReturnType_5011Parser;

   /**
    * @generated
    */
   private IParser getDbcMethodSignatureReturnType_5011Parser() {
      if (dbcMethodSignatureReturnType_5011Parser == null) {
         EAttribute[] features = new EAttribute[] {
               DbcmodelPackage.eINSTANCE.getAbstractDbcOperation_Signature(),
               DbcmodelPackage.eINSTANCE.getDbcMethod_ReturnType() };
         MessageFormatParser parser = new MessageFormatParser(features);
         parser.setViewPattern("{0} : {1}"); //$NON-NLS-1$
         parser.setEditorPattern("{0} : {1}"); //$NON-NLS-1$
         parser.setEditPattern("{0} : {1}"); //$NON-NLS-1$
         dbcMethodSignatureReturnType_5011Parser = parser;
      }
      return dbcMethodSignatureReturnType_5011Parser;
   }

   /**
    * @generated
    */
   private IParser dbcOperationContractName_5035Parser;

   /**
    * @generated
    */
   private IParser getDbcOperationContractName_5035Parser() {
      if (dbcOperationContractName_5035Parser == null) {
         EAttribute[] features = new EAttribute[] { DbcmodelPackage.eINSTANCE
               .getAbstractDbcSpecification_Name() };
         MessageFormatParser parser = new MessageFormatParser(features);
         dbcOperationContractName_5035Parser = parser;
      }
      return dbcOperationContractName_5035Parser;
   }

   /**
    * @generated
    */
   private IParser dbcOperationContractPre_5036Parser;

   /**
    * @generated
    */
   private IParser getDbcOperationContractPre_5036Parser() {
      if (dbcOperationContractPre_5036Parser == null) {
         EAttribute[] features = new EAttribute[] { DbcmodelPackage.eINSTANCE
               .getDbcOperationContract_Pre() };
         MessageFormatParser parser = new MessageFormatParser(features);
         dbcOperationContractPre_5036Parser = parser;
      }
      return dbcOperationContractPre_5036Parser;
   }

   /**
    * @generated
    */
   private IParser dbcOperationContractPost_5037Parser;

   /**
    * @generated
    */
   private IParser getDbcOperationContractPost_5037Parser() {
      if (dbcOperationContractPost_5037Parser == null) {
         EAttribute[] features = new EAttribute[] { DbcmodelPackage.eINSTANCE
               .getDbcOperationContract_Post() };
         MessageFormatParser parser = new MessageFormatParser(features);
         dbcOperationContractPost_5037Parser = parser;
      }
      return dbcOperationContractPost_5037Parser;
   }

   /**
    * @generated
    */
   private IParser dbcConstructorSignature_5012Parser;

   /**
    * @generated
    */
   private IParser getDbcConstructorSignature_5012Parser() {
      if (dbcConstructorSignature_5012Parser == null) {
         EAttribute[] features = new EAttribute[] { DbcmodelPackage.eINSTANCE
               .getAbstractDbcOperation_Signature() };
         MessageFormatParser parser = new MessageFormatParser(features);
         dbcConstructorSignature_5012Parser = parser;
      }
      return dbcConstructorSignature_5012Parser;
   }

   /**
    * @generated
    */
   private IParser dbcEnumLiteralName_5062Parser;

   /**
    * @generated
    */
   private IParser getDbcEnumLiteralName_5062Parser() {
      if (dbcEnumLiteralName_5062Parser == null) {
         EAttribute[] features = new EAttribute[] { DbcmodelPackage.eINSTANCE
               .getDbcEnumLiteral_Name() };
         MessageFormatParser parser = new MessageFormatParser(features);
         dbcEnumLiteralName_5062Parser = parser;
      }
      return dbcEnumLiteralName_5062Parser;
   }

   /**
    * @generated
    */
   private IParser dbcAxiomName_5056Parser;

   /**
    * @generated
    */
   private IParser getDbcAxiomName_5056Parser() {
      if (dbcAxiomName_5056Parser == null) {
         EAttribute[] features = new EAttribute[] { DbcmodelPackage.eINSTANCE
               .getAbstractDbcSpecification_Name() };
         MessageFormatParser parser = new MessageFormatParser(features);
         dbcAxiomName_5056Parser = parser;
      }
      return dbcAxiomName_5056Parser;
   }

   /**
    * @generated
    */
   private IParser dbcAxiomDefinition_5060Parser;

   /**
    * @generated
    */
   private IParser getDbcAxiomDefinition_5060Parser() {
      if (dbcAxiomDefinition_5060Parser == null) {
         EAttribute[] features = new EAttribute[] { DbcmodelPackage.eINSTANCE
               .getDbcAxiom_Definition() };
         MessageFormatParser parser = new MessageFormatParser(features);
         dbcAxiomDefinition_5060Parser = parser;
      }
      return dbcAxiomDefinition_5060Parser;
   }

   /**
    * @generated
    */
   private IParser dbCAxiomContractName_5057Parser;

   /**
    * @generated
    */
   private IParser getDbCAxiomContractName_5057Parser() {
      if (dbCAxiomContractName_5057Parser == null) {
         EAttribute[] features = new EAttribute[] { DbcmodelPackage.eINSTANCE
               .getAbstractDbcSpecification_Name() };
         MessageFormatParser parser = new MessageFormatParser(features);
         dbCAxiomContractName_5057Parser = parser;
      }
      return dbCAxiomContractName_5057Parser;
   }

   /**
    * @generated
    */
   private IParser dbCAxiomContractPre_5058Parser;

   /**
    * @generated
    */
   private IParser getDbCAxiomContractPre_5058Parser() {
      if (dbCAxiomContractPre_5058Parser == null) {
         EAttribute[] features = new EAttribute[] { DbcmodelPackage.eINSTANCE
               .getDbCAxiomContract_Pre() };
         MessageFormatParser parser = new MessageFormatParser(features);
         dbCAxiomContractPre_5058Parser = parser;
      }
      return dbCAxiomContractPre_5058Parser;
   }

   /**
    * @generated
    */
   private IParser dbCAxiomContractDep_5059Parser;

   /**
    * @generated
    */
   private IParser getDbCAxiomContractDep_5059Parser() {
      if (dbCAxiomContractDep_5059Parser == null) {
         EAttribute[] features = new EAttribute[] { DbcmodelPackage.eINSTANCE
               .getDbCAxiomContract_Dep() };
         MessageFormatParser parser = new MessageFormatParser(features);
         dbCAxiomContractDep_5059Parser = parser;
      }
      return dbCAxiomContractDep_5059Parser;
   }

   /**
    * @generated
    */
   private IParser dbcProofReferenceKind_6001Parser;

   /**
    * @generated
    */
   private IParser getDbcProofReferenceKind_6001Parser() {
      if (dbcProofReferenceKind_6001Parser == null) {
         EAttribute[] features = new EAttribute[] { DbcmodelPackage.eINSTANCE
               .getDbcProofReference_Kind() };
         MessageFormatParser parser = new MessageFormatParser(features);
         parser.setViewPattern("«{0}»"); //$NON-NLS-1$
         parser.setEditorPattern("«{0}»"); //$NON-NLS-1$
         parser.setEditPattern("«{0}»"); //$NON-NLS-1$
         dbcProofReferenceKind_6001Parser = parser;
      }
      return dbcProofReferenceKind_6001Parser;
   }

   /**
    * @generated
    */
   protected IParser getParser(int visualID) {
      switch (visualID) {
      case DbcPackageNameEditPart.VISUAL_ID:
         return getDbcPackageName_5042Parser();
      case DbcInterfaceNameEditPart.VISUAL_ID:
         return getDbcInterfaceName_5049Parser();
      case DbcClassNameEditPart.VISUAL_ID:
         return getDbcClassName_5050Parser();
      case DbcEnumNameEditPart.VISUAL_ID:
         return getDbcEnumName_5051Parser();
      case DbcProofObligationEditPart.VISUAL_ID:
         return getDbcProofObligation_5053Parser();
      case DbcPackageName2EditPart.VISUAL_ID:
         return getDbcPackageName_5041Parser();
      case DbcClassName2EditPart.VISUAL_ID:
         return getDbcClassName_5048Parser();
      case DbcInterfaceName2EditPart.VISUAL_ID:
         return getDbcInterfaceName_5047Parser();
      case DbcEnumName2EditPart.VISUAL_ID:
         return getDbcEnumName_5046Parser();
      case DbcProofObligation2EditPart.VISUAL_ID:
         return getDbcProofObligation_5052Parser();
      case DbcInvariantNameEditPart.VISUAL_ID:
         return getDbcInvariantName_5054Parser();
      case DbcInvariantTextEditPart.VISUAL_ID:
         return getDbcInvariantCondition_5055Parser();
      case DbcAttributeNameTypeEditPart.VISUAL_ID:
         return getDbcAttributeNameType_5061Parser();
      case DbcMethodSignatureReturnTypeEditPart.VISUAL_ID:
         return getDbcMethodSignatureReturnType_5011Parser();
      case DbcOperationContractNameEditPart.VISUAL_ID:
         return getDbcOperationContractName_5035Parser();
      case DbcOperationContractPreEditPart.VISUAL_ID:
         return getDbcOperationContractPre_5036Parser();
      case DbcOperationContractPostEditPart.VISUAL_ID:
         return getDbcOperationContractPost_5037Parser();
      case DbcConstructorSignatureEditPart.VISUAL_ID:
         return getDbcConstructorSignature_5012Parser();
      case DbcEnumLiteralNameEditPart.VISUAL_ID:
         return getDbcEnumLiteralName_5062Parser();
      case DbcAxiomNameEditPart.VISUAL_ID:
         return getDbcAxiomName_5056Parser();
      case DbcAxiomDefinitionEditPart.VISUAL_ID:
         return getDbcAxiomDefinition_5060Parser();
      case DbCAxiomContractNameEditPart.VISUAL_ID:
         return getDbCAxiomContractName_5057Parser();
      case DbCAxiomContractPreEditPart.VISUAL_ID:
         return getDbCAxiomContractPre_5058Parser();
      case DbCAxiomContractDepEditPart.VISUAL_ID:
         return getDbCAxiomContractDep_5059Parser();
      case DbcProofReferenceKindEditPart.VISUAL_ID:
         return getDbcProofReferenceKind_6001Parser();
      }
      return null;
   }

   /**
    * Utility method that consults ParserService
    * @generated
    */
   public static IParser getParser(IElementType type, EObject object,
         String parserHint) {
      return ParserService.getInstance().getParser(
            new HintAdapter(type, object, parserHint));
   }

   /**
    * @generated
    */
   public IParser getParser(IAdaptable hint) {
      String vid = (String) hint.getAdapter(String.class);
      if (vid != null) {
         return getParser(DbCVisualIDRegistry.getVisualID(vid));
      }
      View view = (View) hint.getAdapter(View.class);
      if (view != null) {
         return getParser(DbCVisualIDRegistry.getVisualID(view));
      }
      return null;
   }

   /**
    * @generated
    */
   public boolean provides(IOperation operation) {
      if (operation instanceof GetParserOperation) {
         IAdaptable hint = ((GetParserOperation) operation).getHint();
         if (DbCElementTypes.getElement(hint) == null) {
            return false;
         }
         return getParser(hint) != null;
      }
      return false;
   }

   /**
    * @generated
    */
   private static class HintAdapter extends ParserHintAdapter {

      /**
       * @generated
       */
      private final IElementType elementType;

      /**
       * @generated
       */
      public HintAdapter(IElementType type, EObject object, String parserHint) {
         super(object, parserHint);
         assert type != null;
         elementType = type;
      }

      /**
       * @generated
       */
      public Object getAdapter(Class adapter) {
         if (IElementType.class.equals(adapter)) {
            return elementType;
         }
         return super.getAdapter(adapter);
      }
   }

}